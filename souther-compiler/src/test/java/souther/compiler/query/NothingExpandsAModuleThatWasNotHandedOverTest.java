package souther.compiler.query;

import souther.compiler.diag.msg.NameMessage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A question that expands a body of a module asks for a module to expand, and gets nothing where
 * there is none.
 *
 * <p>Expanding a value substitutes its definition at each reference, so a value that reaches itself
 * is substituted into itself: the expansion does not answer, it runs out of stack. What comes back
 * from that is a report about an expression nesting too deeply, which is about nothing the author
 * wrote. So the module has to be known to be well founded before anything expands a body of it.
 *
 * <p>That was a condition each question stated for itself, and one of the three did not. A condition
 * a reader has to remember is a condition a reader can forget, and forgetting it is not caught by
 * compiling a module through the front door: the questions here are asked directly, by name, and
 * two of the three are not on the path a plain compile takes to a report.
 *
 * <p>A row per question that expands. Adding a question that does means adding a row.
 */
class NothingExpandsAModuleThatWasNotHandedOverTest {

    /**
     * A module whose invariant reads a value defined in terms of itself.
     *
     * <p>Read from an invariant rather than from a behavior's body, because that is what reaches the
     * questions about invariants — and those are the ones that read the module directly rather than
     * through what a body was lowered to.
     */
    private static final String CYCLE_UNDER_AN_INVARIANT = """
            module m.a

            let floor = floor

            data Amount = Int
                invariant value >= floor

            data In = { n: Int }
            data Out = { n: Int }

            behavior go : (i: In) -> Out
                constructs Out
            let go (i) = Out { n = i.n }
            """;

    /** The same module with the value defined as a value, so every question below answers. */
    private static final String WELL_FOUNDED =
            CYCLE_UNDER_AN_INVARIANT.replace("let floor = floor", "let floor = 0");

    /** Each question that expands a body of a module, by the answer it is asked for. */
    private static final Map<String, Function<String, Key<?>>> EXPANDING = Map.of(
            "the derived module", Shapes.Derived::new,
            "the clauses of each declaration, expanded", Shapes.ExpandedDeclarationClauses::new,
            "what each clause of an invariant can be discharged by", Shapes.InvariantCapabilities::new,
            "the module a body is prepared from", Shapes.Prepared::new,
            "one body as the backend emits it",
            name -> new Bodies.LoweredBody(name, new souther.compiler.ast.DefinitionName("go")));

    private static Db dbFor(String source) {
        return Compilation.ofDocuments(Map.of("a.sou", source), Set.of(), ModulePath.EMPTY).db();
    }

    @Test
    void noneOfThemExpandsAModuleWhoseValuesAreNotWellFounded() {
        Db db = dbFor(CYCLE_UNDER_AN_INVARIANT);
        for (Map.Entry<String, Function<String, Key<?>>> asked : EXPANDING.entrySet()) {
            assertFalse(db.ask(asked.getValue().apply("m.a")).present(),
                    asked.getKey() + " was answered for a module with a value reaching itself");
        }
    }

    @Test
    void allOfThemAnswerWhenTheyAre() {
        Db db = dbFor(WELL_FOUNDED);
        for (Map.Entry<String, Function<String, Key<?>>> asked : EXPANDING.entrySet()) {
            assertTrue(db.ask(asked.getValue().apply("m.a")).present(),
                    asked.getKey() + " went absent on a module with nothing wrong with it");
        }
    }

    /**
     * And the refusal is still one report, said by the one question that owns it. The others are
     * absent for its reason rather than for one of their own.
     */
    @Test
    void theRefusalIsTheOneTheOwnerSaid() {
        Db db = dbFor(CYCLE_UNDER_AN_INVARIANT);
        EXPANDING.values().forEach(key -> db.ask(key.apply("m.a")));

        List<Report> reports = db.ask(new Shapes.Expandable("m.a")).reports();
        assertFalse(reports.isEmpty(), "the question that owns the rule says what is wrong");
        assertTrue(reports.stream().anyMatch(r -> r.diagnostic() != null
                        && r.diagnostic().said() instanceof NameMessage.AValueReachesItself),
                "and says it as a value cycle: " + reports);
    }
}
