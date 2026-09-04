package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A module's expansion answers for every declaration it wrote, and a declaration with nothing to
 * say answers that it has nothing rather than not answering.
 *
 * <p>This is what makes the other absence unreachable. A reading handed no clauses for a
 * declaration used to fall back to whatever tree it was holding, which is the same shape as a
 * declaration that states little and says nothing about which of the two happened. The fallback is
 * gone, so the question is now whether an answer is always there — and it is, because the expansion
 * is total over what its module declares.
 *
 * <p>Held over the three kinds a module can write, because they reach empty by different routes and
 * a reader must not have to tell them apart: a {@code data} with a clause has it expanded, a
 * {@code data} without one has an empty expansion, and a kind with no {@code invariant} to write
 * ({@link Hir.SumData}, {@link Hir.UnitData}) has nothing to expand at all.
 */
class EveryDeclarationAModuleWritesHasItsClausesExpandedTest {

    private static final String MODEL = """
            module demo

            data Code = String
                invariant shaped = String.length(value) >= 2

            data Plain = { n: Int }

            data Red
            data Blue
            data Colour = Red | Blue
            """;

    private record Read(RuleReadingSource rules, String module) {

        ExpandedClauses of(String name) {
            return rules.invariants().of(new TypeKey(module, name))
                    instanceof ExpandedClauseResult.Found(ExpandedClauses found) ? found : null;
        }
    }

    private static Read read() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        return new Read(RuleReadings.of(compilation, module), module);
    }

    /** Every declaration the model writes, whatever kind it is, has an answer. */
    @Test
    void everyDeclarationHasOne() {
        Read read = read();
        List<String> without = new ArrayList<>();
        for (String name : List.of("Code", "Plain", "Red", "Blue", "Colour")) {
            if (read.of(name) == null) {
                without.add(name);
            }
        }
        assertEquals(List.of(), without,
                "a declaration with no expansion is a reading that could be handed nothing");
    }

    /** The one that wrote a clause has it, expanded. */
    @Test
    void aDeclarationThatWroteAClauseHasIt() {
        ExpandedClauses code = read().of("Code");
        assertNotNull(code);
        assertFalse(code.clauses().isEmpty(), "`Code` writes a clause");
        assertEquals(new TypeKey("demo", "Code"), code.declaration(),
                "and the answer says whose clauses these are");
    }

    /** A product that wrote none reads as none, which is an answer and not a gap. */
    @Test
    void aDeclarationThatWroteNoClauseReadsAsNone() {
        ExpandedClauses plain = read().of("Plain");
        assertNotNull(plain, "`Plain` is declared here");
        assertEquals(List.of(), plain.clauses(),
                "a declaration with no clause has none to read, and is no gap");
    }

    /**
     * A kind with no {@code invariant} to write reads as none too, and reaches it without anyone
     * asking what its module expanded.
     *
     * <p>Only {@link Hir.Data} carries {@code invariants()}, so this is the HIR's answer rather than
     * the expansion's — which is why a sum is answered before there is any question of an
     * environment to expand in.
     */
    @Test
    void aKindWithNoClauseToWriteReadsAsNone() {
        Read read = read();
        for (String name : List.of("Colour", "Red")) {
            ExpandedClauses none = read.of(name);
            assertNotNull(none, name + " is declared here");
            assertTrue(none.clauses().isEmpty(),
                    name + " is a kind with no invariant to write");
        }
    }
}
