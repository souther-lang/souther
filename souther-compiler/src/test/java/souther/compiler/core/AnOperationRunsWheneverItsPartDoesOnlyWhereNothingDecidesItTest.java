package souther.compiler.core;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operation runs whenever the body it is written in does only where nothing decides it: not an
 * arm of a choice, not an arm an attempt takes where the value is built, not the right operand of
 * an operator that stops where its answer is settled, and not the body of a function value, whose
 * body runs where a call applies it, on arguments the position does not have.
 *
 * <p>Asked of the tree a body checks to, the remainders told apart by the number each divides.
 */
class AnOperationRunsWheneverItsPartDoesOnlyWhereNothingDecidesItTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("probe", "evaluated");

    private static final String SOURCE = """
            module probe.evaluated

            data Ok
            data No
            data Tag = String
                invariant String.matches("[a-z]+", value)
            data Held = { s: String, k: Int }

            behavior m : (p: Held) -> Bool
                constructs Tag

            let m (p) = {
                let beside = Int.floorMod(1, p.k)
                let inAnArm = if p.k > 0 then Int.floorMod(3, p.k) else 0
                let whereBuilt = if Tag(p.s) as t then Int.floorMod(4, p.k) else 0
                let afterAnAnd = p.k > 0 && Int.floorMod(5, p.k) > 0
                let afterAnOr = p.k > 0 || Int.floorMod(6, p.k) > 0
                let leftOfAnAnd = Int.floorMod(7, p.k) > 0 && p.k > 0
                p.k > 0
            }
            """;

    private static void remaindersIn(Core in, Map<Long, Core> into) {
        Core here = Core.withoutStanding(in);
        if (here instanceof Core.Call call && call.args().size() == 2
                && Core.withoutStanding(call.args().getFirst())
                        instanceof Core.Int(long dividend, var _, var _)
                && call.fn().toString().contains("floorMod")) {
            into.put(dividend, here);
        }
        Core.forEachChild(here, child -> remaindersIn(child, into));
    }

    private static Map<Long, Core> remainders(Core body) {
        Map<Long, Core> remainders = new LinkedHashMap<>();
        remaindersIn(body, remainders);
        return remainders;
    }

    private static Core bodyOfTheModel() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("m");
        assertNotNull(body, "the behavior under test has a body");
        return body;
    }

    @Test
    void onlyWhatNothingDecidesRunsWheneverTheBodyDoes() {
        Core body = bodyOfTheModel();
        Map<Long, Core> remainders = remainders(body);
        assertTrue(remainders.keySet().containsAll(List.of(1L, 3L, 4L, 5L, 6L, 7L)),
                "each remainder written is in the tree: " + body);

        Map<String, Boolean> runs = new LinkedHashMap<>();
        runs.put("beside", Evaluated.runsWhenever(body, remainders.get(1L)));
        runs.put("inAnArm", Evaluated.runsWhenever(body, remainders.get(3L)));
        runs.put("whereBuilt", Evaluated.runsWhenever(body, remainders.get(4L)));
        runs.put("afterAnAnd", Evaluated.runsWhenever(body, remainders.get(5L)));
        runs.put("afterAnOr", Evaluated.runsWhenever(body, remainders.get(6L)));
        runs.put("leftOfAnAnd", Evaluated.runsWhenever(body, remainders.get(7L)));

        Map<String, Boolean> expected = new LinkedHashMap<>();
        expected.put("beside", true);
        expected.put("inAnArm", false);
        expected.put("whereBuilt", false);
        expected.put("afterAnAnd", false);
        expected.put("afterAnOr", false);
        expected.put("leftOfAnAnd", true);
        assertEquals(expected, runs);
    }

    /**
     * A function value is made where it is written and its body is run where a call applies it, so
     * what stands in the body is not run by the position that makes it — however the body is
     * written, since the account of the order is not the account of the scopes.
     */
    @Test
    void theBodyOfAFunctionValueIsNotRunByTheValueBeingMade() {
        Core operation = remainders(bodyOfTheModel()).get(1L);
        Core.Binder x = new Core.Binder("x", new BindingId(OWNER, 7));
        Core block = new Core.Block(List.of(x), List.of(Type.INT), operation, POS);
        Core made = new Core.ListLit(List.of(block), Type.list(Type.INT), POS);
        Core held = new Core.ListLit(List.of(operation), Type.list(Type.INT), POS);

        assertFalse(Evaluated.runsWhenever(made, operation));
        assertTrue(Evaluated.runsWhenever(held, operation), "where it is no body, it is run");
    }
}
