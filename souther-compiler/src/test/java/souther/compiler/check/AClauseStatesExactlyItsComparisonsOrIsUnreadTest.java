package souther.compiler.check;

import souther.compiler.meta.ModulePath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A clause publishes the comparisons it states exactly, or says it is unread.
 *
 * <p>The fact is the whole clause's: {@code a + b >= 100 && opaque(a, b)} implies a bound on the
 * sum and holds back more than it, so it is unread and not the bound. Held here over the shapes a
 * clause is written in, that a rule is one fact however it is spelled, and that moving a
 * declaration down the file does not move the fact.
 */
class AClauseStatesExactlyItsComparisonsOrIsUnreadTest {

    private static String source(String clause) {
        return """
                module demo.pair exposing ( Pair )

                let opaque (a: Int, b: Int) : Bool = a * b > 3

                data Pair = { a: Int, b: Int }
                    invariant %s
                """.formatted(clause);
    }

    private static ClauseAffineMeaning of(String clause) {
        return ofSource(source(clause));
    }

    private static ClauseAffineMeaning ofSource(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.answerEverything();
        assertEquals(List.of(),
                compilation.errors().stream().map(each -> each.diagnostic().code()).toList(),
                source);
        Db db = compilation.db();
        DeclarationMeaning.Product pair = (DeclarationMeaning.Product) ClauseReadings.meaningOf(db,
                "demo.pair", TypeSymbols.declared(new TypeKey("demo.pair", "Pair")));
        assertEquals(1, pair.clauses().size());
        return ((ClauseMeaning.Stated) pair.clauses().getFirst()).affine();
    }

    private static ClauseAffineMeaning.Comparison sum(long constant, Rel rel, long weightOfA,
                                                      long weightOfB) {
        return new ClauseAffineMeaning.Comparison(
                new LinearForm<>(ExactRatio.of(constant),
                        Map.of(RuleKey.of("a"), ExactRatio.of(weightOfA),
                                RuleKey.of("b"), ExactRatio.of(weightOfB))), rel);
    }

    @Test
    void aSingleComparisonOfASumIsExact() {
        assertEquals(new ClauseAffineMeaning.Exact(List.of(sum(-100, Rel.GE, 1, 1))),
                of("a + b >= 100"));
    }

    /** Which side a number is on, the order the places are added in and how the relation is turned
     *  are the author's spelling and not what the rule says. */
    @Test
    void theSpellingOfARuleIsNotPartOfTheFact() {
        ClauseAffineMeaning written = of("a + b >= 100");
        assertEquals(written, of("b + a >= 100"));
        assertEquals(written, of("a + b - 100 >= 0"));
        assertEquals(written, of("100 <= a + b"));
        assertEquals(new ClauseAffineMeaning.Exact(List.of(sum(-99, Rel.GT, 1, 1))),
                of("99 < a + b"));
    }

    @Test
    void conjunctsOfOneSumAreExactTogether() {
        assertEquals(new ClauseAffineMeaning.Exact(
                        List.of(sum(-100, Rel.GE, 1, 1), sum(-200, Rel.LT, 1, 1))),
                of("a + b >= 100 && a + b < 200"));
        assertEquals(new ClauseAffineMeaning.Exact(
                        List.of(sum(-100, Rel.GE, 1, 1), sum(-200, Rel.LT, 1, 1))),
                of("a + b >= 100 && 2 * a + 2 * b < 400"));
    }

    @Test
    void aWeightedSumIsExact() {
        assertEquals(new ClauseAffineMeaning.Exact(List.of(sum(-100, Rel.GE, 1, 2))),
                of("a + 2 * b >= 100"));
        assertEquals(new ClauseAffineMeaning.Exact(List.of(sum(-100, Rel.GE, 1, -1))),
                of("a - b >= 100"));
    }

    /** What the clause holds back besides the comparison is the point: the bound it implies is not
     *  what it states. */
    @Test
    void aClauseThatStatesMoreThanComparisonsIsUnread() {
        assertEquals(ClauseAffineMeaning.UNREAD, of("a + b >= 100 && opaque(a, b)"));
        assertEquals(ClauseAffineMeaning.UNREAD, of("opaque(a, b)"));
        assertEquals(ClauseAffineMeaning.UNREAD, of("a * b >= 100"));
    }

    @Test
    void aChoiceIsUnread() {
        assertEquals(ClauseAffineMeaning.UNREAD, of("a + b >= 100 || a + b < 0"));
    }

    /** Comparisons of two different sums say how the places stand to one another in two ways. */
    @Test
    void conjunctsOfDifferentSumsAreUnread() {
        assertEquals(ClauseAffineMeaning.UNREAD, of("a + b >= 100 && a - b >= 0"));
    }

    @Test
    void aComparisonOfOnePlaceAloneIsExact() {
        assertInstanceOf(ClauseAffineMeaning.Exact.class, of("a >= 0"));
    }

    @Test
    void movingTheDeclarationDownTheFileDoesNotMoveTheFact() {
        String moved = source("a + b >= 100").replace("data Pair",
                "// a line written above it, which moves every position below\ndata Pair");
        assertEquals(of("a + b >= 100"), ofSource(moved));
        assertNotEquals(of("a + b >= 100"), of("a + b >= 101"));
    }
}
