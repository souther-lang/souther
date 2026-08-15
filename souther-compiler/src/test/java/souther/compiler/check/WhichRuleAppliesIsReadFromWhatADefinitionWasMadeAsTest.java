package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.query.Shapes;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which rules a definition is held to is read from what it was made as, and not from whether its
 * name was spelled in a source.
 *
 * <p>Two unlike things have no spelling. A wrapper minted for a row's operand is one, and so is a
 * definition another module wrote that this one emits under the name it reaches it by — {@code
 * reachedAs} mints a name for it precisely because the reach name is not the declaration's. Asking
 * whether the name was authored answers yes to neither and so cannot tell them apart, and the rules
 * written for the first came to be applied to the second.
 *
 * <p>What is asked instead is what the definition is: an ordinary one, or the value a row writes at
 * a position. A definition made for a position carries that position, so the questions a rule has
 * about it — what the position contributes to reading it, whether it requires the value to be of
 * that type — are asked of the position rather than of a set of names kept alongside.
 */
class WhichRuleAppliesIsReadFromWhatADefinitionWasMadeAsTest {

    private static final String RULES = """
            module rules exposing ( Item, depth )

            data Item = { rank: Int, parent: Item? }

            let depth (i: Item) : Int =
                match i.parent with
                    | Some p -> 1 + depth(p)
                    | None   -> 0
            """;

    private static final String APP = """
            module app exposing ( In, Out, run )

            import rules ( Item, depth )

            data In  = { n: Int }
            data Out = { m: Int }

            behavior run : (i: In) -> Out constructs Out
            let run (i) = Out { m = i.n }

            example run
                | "a row applies a recursion" : (In { n = depth(Item { rank = 0 }) }) -> Out { m = 0 }
            """;

    private static Prepared prepared() {
        Db db = Compilation.ofDocuments(Map.of("rules.sou", RULES, "app.sou", APP),
                Set.of(), ModulePath.EMPTY).db();
        Answer<Prepared> answer = db.ask(new Shapes.Prepared("app"));
        assertTrue(answer.present(), "prepared of app: " + answer.reports());
        return answer.value();
    }

    private static Hir.FnDef definition(Hir.Module module, String name) {
        for (Hir.FnDef fn : module.takenOn()) {
            if (fn.name().equals(name)) {
                return fn;
            }
        }
        for (Hir.FnDef fn : module.fns()) {
            if (fn.name().equals(name)) {
                return fn;
            }
        }
        throw new AssertionError("`" + name + "` is not a definition of " + module.name());
    }

    @Test
    void aDefinitionMintedForARowPositionSaysThatIsWhatItIs() {
        Prepared state = prepared();

        for (String method : state.operandMethods().values()) {
            assertInstanceOf(DefinitionRole.RowValue.class,
                    definition(state.tree(), method).role(), method);
        }
    }

    @Test
    void aDefinitionAnotherModuleWroteIsOrdinaryHoweverThisOneNamesIt() {
        Prepared state = prepared();
        Hir.FnDef taken = definition(state.tree(), "rules.depth");

        assertInstanceOf(DefinitionRole.Ordinary.class, taken.role());
        assertFalse(taken.written().authored(),
                "and its name is unauthored, which is the reading this replaces");
    }

    @Test
    void aDefinitionTheModuleWroteIsOrdinaryToo() {
        assertInstanceOf(DefinitionRole.Ordinary.class,
                definition(prepared().tree(), "run").role());
    }

    @Test
    void anInputPositionRequiresItsTypeAndAnExpectationDoesNot() {
        // The row writes one input and one expectation. A row may state what the behavior does not
        // answer with — reporting that disagreement is what the row is for — so the expectation's
        // position contributes a type and requires nothing, while the input's does both.
        Prepared state = prepared();
        List<RowPosition> positions = new ArrayList<>();
        for (String method : state.operandMethods().values()) {
            positions.add(((DefinitionRole.RowValue) definition(state.tree(), method).role())
                    .position());
        }

        assertEquals(2, positions.size(), "one input and one expectation");
        assertEquals(1, positions.stream().filter(p -> p.required() != null).count(),
                "the input requires its type");
        assertTrue(positions.stream().allMatch(p -> p.contextual() != null),
                "and both contribute one");
    }
}
