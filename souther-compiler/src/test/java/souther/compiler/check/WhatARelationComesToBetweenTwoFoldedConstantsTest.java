package souther.compiler.check;

import souther.compiler.numeric.Rel;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What each relation comes to between two folded constants.
 *
 * <p>Two questions, held apart. What a relation answers is decided by how the two values stand —
 * below one another, at one another, above, or of no ordered kind at all — and by nothing else, so
 * the meaning is fixed against those five ways of standing. Which values stand which way is the
 * other question: each ordered kind is read by its own comparison, and a kind put through one
 * ordering says nothing about the other two.
 *
 * <p>Read one table at a time, so a kind whose ordering moved is told apart from a relation whose
 * meaning did.
 *
 * <p><b>Which relations there are is asked of {@link Rel}.</b> Written out here, a relation added
 * to it would be answered about by nothing while these tables went on saying "each".
 */
class WhatARelationComesToBetweenTwoFoldedConstantsTest {

    /** Every relation, asked of the type that has them. */
    private static final List<Rel> RELATIONS = List.of(Rel.values());

    /** What a relation two constants cannot answer is said as. */
    private static final String UNDECIDED = "undecided";

    /** A way two values can stand, and what each relation answers of two values standing so. */
    private record Standing(String name, Map<Rel, String> answers) { }

    private static final List<Standing> STANDINGS = List.of(
            new Standing("below", Map.of(
                    Rel.EQ, "false", Rel.NE, "true", Rel.LT, "true", Rel.LE, "true",
                    Rel.GT, "false", Rel.GE, "false")),
            new Standing("at", Map.of(
                    Rel.EQ, "true", Rel.NE, "false", Rel.LT, "false", Rel.LE, "true",
                    Rel.GT, "false", Rel.GE, "true")),
            new Standing("above", Map.of(
                    Rel.EQ, "false", Rel.NE, "true", Rel.LT, "false", Rel.LE, "false",
                    Rel.GT, "true", Rel.GE, "true")),
            // An equality answers of any two constants at all, and an ordering is not something to
            // decide where there is no order to decide it by.
            new Standing("of no ordered kind, one value", Map.of(
                    Rel.EQ, "true", Rel.NE, "false", Rel.LT, UNDECIDED, Rel.LE, UNDECIDED,
                    Rel.GT, UNDECIDED, Rel.GE, UNDECIDED)),
            new Standing("of no ordered kind, two values", Map.of(
                    Rel.EQ, "false", Rel.NE, "true", Rel.LT, UNDECIDED, Rel.LE, UNDECIDED,
                    Rel.GT, UNDECIDED, Rel.GE, UNDECIDED)));

    /** Two folded values, how they stand, and how they are named in a row. */
    private record Pair(String name, Object left, Object right, String stands) { }

    /** One pair for each way of standing, over the kind an ordering is written of most. */
    private static final List<Pair> EACH_WAY_OF_STANDING = List.of(
            new Pair("1 and 2", 1L, 2L, "below"),
            new Pair("2 and 2", 2L, 2L, "at"),
            new Pair("2 and 1", 2L, 1L, "above"),
            new Pair("true and true", true, true, "of no ordered kind, one value"),
            new Pair("true and false", true, false, "of no ordered kind, two values"));

    /** The kinds that carry an ordering of their own, each put through all three of them. */
    private static final List<Pair> EACH_ORDERED_KIND = List.of(
            new Pair("1.0m and 2.0m", decimal("1.0"), decimal("2.0"), "below"),
            // Written differently and the one amount, which is what a decimal is compared by.
            new Pair("1.0m and 1.00m", decimal("1.0"), decimal("1.00"), "at"),
            new Pair("2.0m and 1.0m", decimal("2.0"), decimal("1.0"), "above"),
            new Pair("\"a\" and \"b\"", "a", "b", "below"),
            new Pair("\"a\" and \"a\"", "a", "a", "at"),
            new Pair("\"b\" and \"a\"", "b", "a", "above"));

    /** Pairs of no one ordered kind, which is where an equality answers alone. */
    private static final List<Pair> OF_NO_ORDERED_KIND = List.of(
            new Pair("false and false", false, false, "of no ordered kind, one value"),
            new Pair("false and true", false, true, "of no ordered kind, two values"),
            new Pair("1 and 1.0m", 1L, decimal("1.0"), "of no ordered kind, two values"));

    @Test
    void howTheTwoStandDecidesWhatEachRelationAnswers() {
        assertEquals(written(EACH_WAY_OF_STANDING), answered(EACH_WAY_OF_STANDING),
                "what a relation answers is read off how the two values stand and nothing else");
    }

    @Test
    void everyOrderedKindStandsTheWayItsOwnComparisonSays() {
        assertEquals(written(EACH_ORDERED_KIND), answered(EACH_ORDERED_KIND),
                "a kind whose values are put in the wrong order answers every relation about them"
                        + " consistently and about the wrong pair");
    }

    @Test
    void twoValuesOfNoOneOrderedKindAnswerTheEqualityAlone() {
        assertEquals(written(OF_NO_ORDERED_KIND), answered(OF_NO_ORDERED_KIND),
                "an ordering of values there is no order over is undecided, and an equality of them"
                        + " is not");
    }

    /**
     * Of two values of one ordered kind, the equality answers what being one value answers.
     *
     * <p>The two are asked in different words — where the values stand, and whether they are the
     * one value ({@link ConstEval#equal}) — and an equality of such a pair is answered in the
     * first, so what makes that the whole answer is that the two agree. A decimal is where they
     * could come apart, since {@code 1.0m} and {@code 1.00m} are two ways of writing one amount,
     * and both answers are the amount's.
     */
    @Test
    void ofOneOrderedKindTheEqualityAnswersWhatBeingOneValueAnswers() {
        assertEquals(List.of(
                "1 and 2: EQ = false, NE = true, one value = false",
                "2 and 2: EQ = true, NE = false, one value = true",
                "2 and 1: EQ = false, NE = true, one value = false",
                "1.0m and 2.0m: EQ = false, NE = true, one value = false",
                "1.0m and 1.00m: EQ = true, NE = false, one value = true",
                "2.0m and 1.0m: EQ = false, NE = true, one value = false",
                "\"a\" and \"b\": EQ = false, NE = true, one value = false",
                "\"a\" and \"a\": EQ = true, NE = false, one value = true",
                "\"b\" and \"a\": EQ = false, NE = true, one value = false"),
                bothWays());
    }

    /**
     * What is written above is an answer for each relation there is, and for no other.
     *
     * <p>The two sets are made differently on purpose — one is asked of {@link Rel}, the other is
     * what somebody wrote out — so holding them against each other is what says a relation added
     * later is answered about here rather than passed over. It is also what says the tables above
     * were read at all: two empty sets agree, and these do not.
     */
    @Test
    void whatIsWrittenOutCoversEveryRelationThereIs() {
        List<Set<Rel>> asked = new ArrayList<>();
        List<Set<Rel>> answered = new ArrayList<>();
        for (Standing each : STANDINGS) {
            asked.add(Set.copyOf(RELATIONS));
            answered.add(each.answers().keySet());
        }
        assertEquals(asked, answered,
                "a relation no way of standing writes an answer for is fixed by nothing");
    }

    private static List<String> bothWays() {
        List<Pair> pairs = new ArrayList<>(EACH_WAY_OF_STANDING.subList(0, 3));
        pairs.addAll(EACH_ORDERED_KIND);
        return pairs.stream().map(each -> each.name()
                + ": EQ = " + ConstEval.stands(Rel.EQ, each.left(), each.right())
                + ", NE = " + ConstEval.stands(Rel.NE, each.left(), each.right())
                + ", one value = " + ConstEval.equal(each.left(), each.right())).toList();
    }

    /** What each relation answers of each pair, taken from the way it stands. */
    private static Map<String, String> written(List<Pair> pairs) {
        Map<String, String> rows = new LinkedHashMap<>();
        for (Pair pair : pairs) {
            Map<Rel, String> answers = standing(pair.stands()).answers();
            for (Rel rel : RELATIONS) {
                rows.put(row(pair, rel), answers.get(rel));
            }
        }
        return rows;
    }

    /** What each relation answers of each pair, taken from the fold. */
    private static Map<String, String> answered(List<Pair> pairs) {
        Map<String, String> rows = new LinkedHashMap<>();
        for (Pair pair : pairs) {
            for (Rel rel : RELATIONS) {
                Boolean stands = ConstEval.stands(rel, pair.left(), pair.right());
                rows.put(row(pair, rel), stands == null ? UNDECIDED : String.valueOf(stands));
            }
        }
        return rows;
    }

    private static String row(Pair pair, Rel rel) {
        return pair.name() + " (" + pair.stands() + ") " + rel;
    }

    private static Standing standing(String name) {
        return STANDINGS.stream().filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow(() -> new IllegalArgumentException("no way of standing named " + name));
    }

    private static BigDecimal decimal(String written) {
        return new BigDecimal(written);
    }
}
