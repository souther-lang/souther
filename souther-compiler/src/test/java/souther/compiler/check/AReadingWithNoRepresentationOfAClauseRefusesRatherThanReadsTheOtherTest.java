package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A declaration whose reading did not arrive is refused, and not read in the other representation.
 *
 * <p>The two forms of a clause are the same text and different trees, and what a reader gets used to
 * be decided by whether a constructor was handed a map: handed none, it read the tree the backend
 * emits from and said nothing about it. The failure that leaves is silent — a declaration read in the
 * wrong form states less, which is what a declaration read in the right form and found to state
 * little also looks like.
 *
 * <p>So the absence is refused where it is met, and refused as a disagreement rather than as a
 * limit: the reading below falls open on any shape it has no rule for, and a failure that did not
 * carry {@link souther.compiler.diag.TheCompilerDisagreesWithItself} would be swallowed there and
 * come back as a reading that managed nothing.
 *
 * <p>Written as a reading with one declaration held back, because that is the state the type exists
 * to make unreachable and there is no other way to reach it. A model another module declares is not
 * this: it has no reading here and never did, and reads in the form that travels with it.
 */
class AReadingWithNoRepresentationOfAClauseRefusesRatherThanReadsTheOtherTest {

    private static final String MODEL = """
            module demo

            data Code = String
                invariant shaped = String.length(value) >= 2
            """;

    /** The reading of {@code demo}, with the clauses of {@code Code} taken back out of it. */
    private static AnalysisInvariants withCodeHeldBack(Compilation compilation, String module) {
        AnalysisInvariants whole = RuleReadings.of(compilation, module).invariants();
        Map<TypeSymbol.AtModule, List<Hir.InvariantClause>> kept = new LinkedHashMap<>();
        // Nothing of `Code`, which is the one declaration this model writes a clause on.
        return new AnalysisInvariants(whole.module(), kept);
    }

    @Test
    void aDeclarationWhoseClausesAreMissingIsRefused() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = RuleReadings.of(compilation, module).symbols();
        TypeSymbol.AtModule code = TypeSymbols.declared(new TypeKey(module, "Code"));
        Hir.Data data = (Hir.Data) symbols.declaredNode(code.key());
        assertNotNull(data, "the model under test declares `Code`");
        assertTrue(!data.invariants().isEmpty(), "and writes a clause on it");

        AnalysisInvariants held = withCodeHeldBack(compilation, module);

        AnalysisInvariants.NothingWasFiledFor refused =
                assertThrows(AnalysisInvariants.NothingWasFiledFor.class,
                        () -> held.clausesOf(code, data),
                        "a declaration of this module that wrote clauses and has none here is this"
                                + " compiler having failed to hand its own reading over");
        assertTrue(refused.getMessage().contains("Code"), () -> refused.getMessage());
    }

    /** And a declaration that wrote no clause is not that: it has none to read. */
    @Test
    void aDeclarationThatWroteNoClauseReadsAsNone() {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data Plain = { n: Int }
                """, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        TypeSymbol.AtModule plain = TypeSymbols.declared(new TypeKey(module, "Plain"));
        Hir.Data data = (Hir.Data) rules.symbols().declaredNode(plain.key());

        assertEquals(List.of(), rules.invariants().clausesOf(plain, data),
                "a declaration with no clause has none to read, and is no gap");
    }
}
