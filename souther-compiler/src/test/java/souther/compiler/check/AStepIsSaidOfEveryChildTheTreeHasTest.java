package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * {@link ScopeStep#forEachChild} hands over the children {@link Core#forEachChild} does, in the same
 * order, and says of each what entering it does to the names in force.
 *
 * <p>Which slots a node has is {@code Core}'s answer. The nodes that change what a name means are
 * written out a second time where the step into each slot is said, and a slot added to one of them
 * in {@code Core} and not there would be walked by nothing that carries an environment. The
 * exhaustive switch stops a node kind being missed; this stops a slot being missed.
 *
 * <p>And the step is held as well as the slot, on both sides of it. A name an attempt binds is in
 * force in its {@code then} and nowhere else: not in the construction, which is evaluated before
 * anything is built, and not in a departure, which is taken where nothing was. Neither of those can
 * be written in a model, since no source names the binder there, so a step wrong on either side is
 * one no observation of a compiled model would see. What a step names is the node it was made from
 * and not one that only looks like it.
 *
 * <p>Over a body that holds each of the ways a step is said, which is checked rather than taken on
 * trust: a model that stopped holding one would leave this green about nothing.
 */
class AStepIsSaidOfEveryChildTheTreeHasTest {

    private static final String MODEL = """
            module demo
            data Q = Int
                invariant value >= 0
            data Red
            data Green
            data Color = Red | Green
            data Item = { n: Int }
            data Nope
            data Yes
            data No
            behavior f : (x: Int, c: Color, items: List<Item>) -> Yes | No | Nope
                constructs Q
            let f (x, c, items) = {
                let big = List.filter(i -> i.n > 3, items)
                guard Q(x) as q else Nope
                match c with
                    | Red -> if q.value > List.length(big) then Yes else No
                    | Green -> No
            }
            """;

    /** Every way a step is said, which the body has to hold each of. */
    private static final Set<String> WAYS = Set.of("Same", "Let", "Block", "ACondition(true)",
            "ACondition(false)", "ACase", "ItWasBuilt", "ItDeparted");

    @Test
    void everyChildHasTheStepThatSlotOfItsNodeIsEnteredBy() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get("f");
        assertNotNull(body, "the behavior under test has a body");

        Set<String> met = new TreeSet<>();
        compare(body, met);

        assertEquals(new TreeSet<>(WAYS), met, "the body holds each way a step is said");
    }

    private static void compare(Core e, Set<String> met) {
        if (e == null) {
            return;
        }
        List<Core> tree = new ArrayList<>();
        Core.forEachChild(e, tree::add);
        List<Core> stepped = new ArrayList<>();
        List<ScopeStep> steps = new ArrayList<>();
        ScopeStep.forEachChild(e, (child, step) -> {
            stepped.add(child);
            steps.add(step);
        });

        assertEquals(tree.size(), stepped.size(), () -> "the children of " + e);
        for (int i = 0; i < tree.size(); i++) {
            assertSame(tree.get(i), stepped.get(i), "child " + i + " of " + e);
            met.add(checkStep(e, i, steps.get(i)));
        }
        tree.forEach(child -> compare(child, met));
    }

    /** That slot {@code slot} of {@code e} is entered by {@code step}, and how it was said. */
    private static String checkStep(Core e, int slot, ScopeStep step) {
        String where = "slot " + slot + " of " + e.getClass().getSimpleName();
        return switch (e) {
            case Core.If iff -> switch (slot) {
                case 0 -> same(step, where);
                case 1 -> condition(step, iff, true, where);
                case 2 -> condition(step, iff, false, where);
                default -> throw new AssertionError(where);
            };
            case Core.IfConstructed ic -> {
                if (slot == 0) {
                    yield same(step, where);
                }
                Choice.Decides decided = chosen(step, where);
                if (slot == 1) {
                    var built = assertInstanceOf(Choice.Decides.ItWasBuilt.class, decided, where);
                    assertSame(ic, built.attempt(), where);
                    yield "ItWasBuilt";
                }
                var departed = assertInstanceOf(Choice.Decides.ItDeparted.class, decided, where);
                assertSame(ic, departed.attempt(), where);
                assertSame(ic.els().get(slot - 2), departed.on(), where);
                yield "ItDeparted";
            }
            case Core.LetIn li -> {
                if (slot == 0) {
                    yield same(step, where);
                }
                assertSame(li, assertInstanceOf(ScopeStep.Let.class, step, where).binding(), where);
                yield "Let";
            }
            case Core.Block b -> {
                assertSame(b, assertInstanceOf(ScopeStep.Block.class, step, where).block(), where);
                yield "Block";
            }
            case Core.Match m -> {
                if (slot == 0) {
                    yield same(step, where);
                }
                var arm = assertInstanceOf(Choice.Decides.ACase.class, chosen(step, where), where);
                assertSame(m.cases().get(slot - 1), arm.arm(), where);
                assertSame(m.scrutinee(), arm.scrutinee(), where);
                yield "ACase";
            }
            default -> same(step, where);
        };
    }

    private static String same(ScopeStep step, String where) {
        assertInstanceOf(ScopeStep.Same.class, step, where);
        return "Same";
    }

    private static Choice.Decides chosen(ScopeStep step, String where) {
        return assertInstanceOf(ScopeStep.Chosen.class, step, where).decidedBy();
    }

    private static String condition(ScopeStep step, Core.If iff, boolean holding, String where) {
        var decided = assertInstanceOf(Choice.Decides.ACondition.class, chosen(step, where), where);
        assertSame(iff.cond(), decided.cond(), where);
        assertEquals(holding, decided.holding(), where);
        return "ACondition(" + holding + ")";
    }
}
