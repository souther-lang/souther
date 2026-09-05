package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The two representations of a clause differ by what was expanded and by nothing else.
 *
 * <p>Both are built from the same declarations by the same steps, and only {@link InliningPolicy}
 * tells them apart. Writing a value's declaration to build one is a construction in either — the
 * spelling {@code T(v)} means a construction wherever it is written, and every stage downstream is
 * written to meet it as one ({@link NewtypeDesugar}).
 *
 * <p>Held by asking the normalising step whether there is anything left for it to do. A clause that
 * still holds an application of a declaration's name is one the step has not been over, and it comes
 * out here as the step changing something. Said that way rather than by walking the tree looking for
 * the shape, because a walk written here would be a second reading of what a construction is, free
 * to disagree with the one the compiler uses.
 *
 * <p>The declaration below writes its construction inside a helper and not in the clause. That is
 * the case a representation built by normalising the clause as written and expanding afterwards
 * gets wrong: the construction is not in the clause when the normalising goes past, and it is in it
 * by the time anything reads it.
 */
class AConstructionIsWrittenAsOneInTheAnalysisRepresentationTest {

    private static final String CONSTRUCTED_IN_A_HELPER = """
            module demo
            data Limit = Int
                invariant value > 0
            data Amount = { n: Int }
                invariant ok(n)
            let ok (n: Int) : Bool = Limit(n).value > 0
            behavior f : (a: Amount) -> Int
            let f (a) = a.n
            """;

    private static final String CONSTRUCTED_IN_THE_CLAUSE = """
            module demo
            data Code = String
                invariant String.length(value) >= 2
            data Tagged = { code: String }
                invariant Code(code).value == code
            behavior f : (t: Tagged) -> String
            let f (t) = t.code
            """;

    @Test
    void aConstructionInsideAHelperIsOneByTheTimeTheClauseIsRead() {
        assertNothingLeftToNormalize(CONSTRUCTED_IN_A_HELPER);
    }

    @Test
    void aConstructionWrittenInTheClauseIsOneToo() {
        assertNothingLeftToNormalize(CONSTRUCTED_IN_THE_CLAUSE);
    }

    private static void assertNothingLeftToNormalize(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        Hir.Module settled = compilation.db().ask(new Bodies.Lowering("demo")).value().settled();

        int held = 0;
        for (Hir.Def def : settled.defs()) {
            if (!(def instanceof Hir.Data data) || data.invariants().isEmpty()) {
                continue;
            }
            ExpandedClauseResult expanded = rules.invariants().of(data.declares().key());
            assertInstanceOf(ExpandedClauseResult.Found.class, expanded,
                    data.declares() + " is read in the representation its module expanded");
            List<Hir.InvariantClause> read =
                    ((ExpandedClauseResult.Found) expanded).clauses().clauses().stream()
                            .map(ExpandedClauses.Expanded::clause).toList();
            Hir.Def again = NewtypeDesugar.rewriteInvariantsOf(
                    new Hir.Data(data.written(), data.declares(), data.newtype(), data.includes(),
                            data.fields(), read, data.pos()),
                    rules.symbols());
            assertEquals(read, ((Hir.Data) again).invariants(),
                    "the analysis representation of " + data.declares() + " writes its "
                            + "constructions as constructions, so normalizing it again is nothing");
            held++;
        }
        assertTrue(held >= 2, "both declarations of the model state a rule: " + held);
    }
}
