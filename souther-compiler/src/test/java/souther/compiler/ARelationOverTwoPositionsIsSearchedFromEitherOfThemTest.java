package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rule between two positions is answered from either of them.
 *
 * <p>Which of the two a search settles before asking the other is the search's own arrangement and
 * is no part of what the rule said. Settling the same one of them always, the compiler could
 * compose a pair for a relation written one way round and not for the same relation written the
 * other — because the order the two positions are on names a value above any of its own and none
 * below one, so the position that has to stand lower is the one a search must settle first.
 *
 * <p><b>Over the order that makes the difference visible and over the one that hides it.</b> Every
 * string has a next string and none has a previous one; whole numbers have both. So a search that
 * settles one position and steps outward from it reaches the pair over the whole numbers whichever
 * way it settled, and the arrangement it was making shows only on the strings. Both carriers are
 * here because a check that ran on the second alone would pass over the defect it is for.
 *
 * <p>Read off the searches and not off the report's prose. What a point came to is what the
 * assessment holds, and a line printed for a reader says less: the two ways of coming back
 * empty-handed print alike until a reader goes looking for which of them happened.
 */
class ARelationOverTwoPositionsIsSearchedFromEitherOfThemTest {

    /**
     * A guard comparing two positions of one order, with nothing else said about either.
     *
     * <p>Both positions unrestricted on purpose. What is being asked is whether the pair can be
     * composed at all, and a rule that narrowed either of them would be a second thing the answer
     * could turn on.
     */
    private static String comparing(String type, String guard) {
        return """
                module m

                data Yes = { v: Int }
                data No = { why: Int }

                behavior cmp : (a: %s, b: %s) -> Yes | No
                    constructs Yes
                    constructs No
                let cmp (a, b) = {
                    guard %s else No { why = 0 }
                    Yes { v = 1 }
                }
                """.formatted(type, type, guard);
    }

    /**
     * Neither side of the line is a point the search settled nothing about.
     *
     * <p>Both sides are inhabited, and by one pair of values read the two ways round: there are
     * strings above any string, so for any {@code a} there is a {@code b} above it and the same two
     * satisfy {@code a < b} and {@code b > a}. So a point coming back with nothing composed and no
     * limit is this compiler saying the question was never narrowed, of a line every value of the
     * order lies on one side of.
     *
     * <p><b>What is refused is the word and not an empty hand.</b> A search may still come back
     * without a pair — what it may not do is come back the way a search that narrowed nothing does,
     * because that is the answer a reader takes for the rules leaving no pair there.
     */
    @Test
    void neitherSideOfALineOverStringsIsLeftUnnarrowed() {
        for (String guard : List.of("a < b", "a > b", "b < a", "b > a")) {
            String model = comparing("String", guard);
            Map<String, String> outcomes = outcomesOf(model);
            assertFalse(outcomes.containsValue(ItemAssessment.Attempt.Unresolved.class.getSimpleName()),
                    () -> "`" + guard + "` over strings: " + outcomes);
        }
    }

    /**
     * The same relation written the other way round is answered the same way.
     *
     * <p>Operand swap and relation inversion together, which is one relation said twice: {@code a <
     * b} and {@code b > a} hold of the same pairs, and the border they draw has the same points
     * asking the same things. So what each point came to may not turn on which of the two an author
     * typed.
     *
     * <p>Point by point rather than as a count. Two models whose points came to the same kinds of
     * answer in a different arrangement are two different answers about the same border, and a
     * check over the multiset would call them one.
     */
    @Test
    void writingARelationTheOtherWayRoundSettlesTheSamePoints() {
        for (String type : List.of("String", "Int")) {
            for (String[] pair : new String[][] {{"a < b", "b > a"}, {"a > b", "b < a"}}) {
                Map<String, String> one = outcomesOf(comparing(type, pair[0]));
                Map<String, String> other = outcomesOf(comparing(type, pair[1]));
                assertEquals(one, other,
                        () -> type + ": `" + pair[0] + "` and `" + pair[1] + "` are one relation");
            }
        }
    }

    /**
     * Whole numbers answer the way strings do, which is what says the answer is about the relation.
     *
     * <p>The negative control this check needs is not a model where the two sides differ — bounds
     * tied to one operand make them differ for a reason the property is not about. It is an order
     * where the defect could not show: a carrier whose values step reaches the pair from either
     * position, so a run that fails here is a run where something other than the arrangement under
     * test moved.
     */
    @Test
    void theSameLineOverWholeNumbersIsSettledAlike() {
        assertEquals(outcomesOf(comparing("Int", "a < b")).values().stream().distinct().sorted()
                        .toList(),
                outcomesOf(comparing("String", "a < b")).values().stream().distinct().sorted()
                        .toList(),
                "a line between two positions is answered the same way on either order");
    }

    /**
     * What each point of the behavior's one border came to, by the point it is.
     *
     * <p>Keyed by the role and the criterion together, because a role names which point of the line
     * this is and the criterion says what it asks for — and the two relations under test put
     * different criteria under the same roles.
     */
    private static Map<String, String> outcomesOf(String model) {
        Map<String, String> out = new LinkedHashMap<>();
        for (BorderAssessment.Point point : pointsOf(model)) {
            ItemAssessment.Owed owed = point.owed();
            if (owed == null) {
                continue;
            }
            ItemAssessment.Attempt attempt = owed.searches().only();
            out.put(point.role().name(),
                    attempt == null ? "none" : attempt.getClass().getSimpleName());
        }
        return out;
    }

    private static List<BorderAssessment.Point> pointsOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.ALL));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.searchedBoundariesOf(compilation.db(), "m");
        assertNotNull(boundaries, "the model under test compiles");
        return BorderAssessment.pointsOf(boundaries.get("cmp"));
    }
}
