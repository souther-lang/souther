package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.source.SourceId;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A point of a border drawn on a total has a row composed for it, and the row comes to the total.
 *
 * <p>Every such point used to be reported as one nothing composed a row for, whichever way the total
 * was written and however plainly an author could write the row by hand. What a search hands back is
 * a value at a location, and the total of a run is answered by none — so the whole of what was
 * missing was somewhere to put the answer, and the answer is the container the values come from.
 *
 * <p><b>Three claims, and the third is what makes the first worth having.</b> A row is composed; the
 * model holds it; and the point it was composed for is met once it is in. A row that carries the
 * total and breaks a rule the elements are under is refused by the compiler that reads it back, and
 * one that carries the wrong total meets no point — both would leave a report saying an edge is
 * writable where nobody can write it.
 *
 * <p>The shapes here are the ones the two halves of the question take. A total of a list at a
 * position adds up what the list holds; a total over a run adds up a path inside each element; and
 * the elements have rules of their own, which is what makes the count of them something to choose
 * rather than one element carrying the whole of it.
 */
class ARowIsComposedForAPointOnATotalTest {

    /** The answer written beside a composed row, which is not what this is about. A row is offered
     *  with its result for an author to fill in, and an example line needs one. */
    private static final String WHATEVER = "Yes";

    /** A row whose stated answer is wrong, which is the one thing said about these rows that is not
     *  being asked: the run reached the comparison to disagree at all. */
    private static final String THE_ANSWER_DISAGREES = "E1905";

    private static final String MODULE = "example.totals";

    private static final String MODEL = """
            module example.totals

            data Amount = Int
                invariant value >= 0

            data Small = Int
                invariant value >= 0
                invariant value <= 10

            data Money = Decimal
                invariant value > 0m

            data NotFour = Int
                invariant value >= 0
                invariant value <= 10
                invariant value /= 4

            data Item = { amount: Amount }
            data Capped = { small: Small }

            data Ledger = { lines: List<Item> }
                invariant List.length(lines) >= 2

            data Pair = { xs: List<NotFour> }

            data Awkward = Int
                invariant value >= 0
                invariant value <= 10
                invariant value /= 3
                invariant value /= 4
                invariant value /= 7

            data Two = { xs: List<Awkward> }
                invariant List.length(xs) == 2

            data Yes
            data No
            data Verdict = Yes | No

            behavior overABareList : (ns: List<Int>) -> Verdict
            let overABareList (ns) =
                if List.sum(ns) >= 100000 then Yes else No

            behavior overAProjection : (lines: List<Item>) -> Verdict
            let overAProjection (lines) =
                if List.sum(List.map(line -> line.amount.value, lines)) >= 100000
                    then Yes else No

            let total (ls: List<Capped>): Int =
                List.sum(List.map(l -> l.small.value, ls))

            behavior needingSeveral : (ls: List<Capped>) -> Verdict
            let needingSeveral (ls) =
                if total(ls) >= 100 then Yes else No

            behavior overADenseRunHeldAwayFromNought : (ds: List<Money>) -> Verdict
            let overADenseRunHeldAwayFromNought (ds) =
                if List.sum(List.map(d -> d.value, ds)) >= 0.5m then Yes else No

            behavior aContainerTheRecordCounts : (l: Ledger) -> Verdict
            let aContainerTheRecordCounts (l) =
                if List.sum(List.map(i -> i.amount.value, l.lines)) >= 100000 then Yes else No

            behavior aTotalBelowWhereItsElementsStart : (ns: List<Int>) -> Verdict
            let aTotalBelowWhereItsElementsStart (ns) =
                if List.sum(ns) >= (0 - 1) then Yes else No

            behavior aTotalTheOneSidedSplitCannotReach : (p: Pair) -> Verdict
            let aTotalTheOneSidedSplitCannotReach (p) =
                if List.sum(List.map(x -> x.value, p.xs)) >= 4 then Yes else No

            behavior noShapeOfferedReachesIt : (t: Two) -> Verdict
            let noShapeOfferedReachesIt (t) =
                if List.sum(List.map(x -> x.value, t.xs)) >= 7 then Yes else No
            """;

    private static final List<String> ON_A_TOTAL =
            List.of("overABareList", "overAProjection", "needingSeveral",
                    "overADenseRunHeldAwayFromNought", "aContainerTheRecordCounts",
                    "aTotalBelowWhereItsElementsStart", "aTotalTheOneSidedSplitCannotReach");

    /** Every point of a line drawn on a total has one. */
    @Test
    void everyPointOnATotalHasARowComposedForIt() {
        Map<String, List<String>> without = new LinkedHashMap<>();
        for (String behavior : ON_A_TOTAL) {
            List<String> owed = new ArrayList<>();
            forEachPoint(behavior, (point, item) -> {
                // A point nothing owes is not one this composes for. An order with no value beside
                // the one a line is drawn at owes no point off it, which is the order's answer and
                // was the order's answer before any of this.
                if (item instanceof ItemAssessment.Owed one
                        && !(one.attempt() instanceof ItemAssessment.Attempt.Built)) {
                    owed.add(point);
                }
            });
            if (!owed.isEmpty()) {
                without.put(behavior, owed);
            }
        }

        assertEquals(Map.of(), without,
                "a point on a total is a point a row can be composed for, whichever way the total"
                        + " is written");
    }

    /** And what is composed is a row the model holds. */
    @Test
    void everyRowComposedIsOneTheModelHolds() {
        Map<String, List<String>> refused = new LinkedHashMap<>();
        forEachComposedRow((behavior, point, row) -> {
            List<String> said = otherThanTheAnswer(MODEL + example(behavior, row));
            if (!said.isEmpty()) {
                refused.put(point + " -> " + row, said);
            }
        });

        assertEquals(Map.of(), refused,
                "the elements are composed under their own rules, so the row is one the module's own"
                        + " decoder takes");
    }

    /** And it stands at the point it was composed for, which is the total coming out right. */
    @Test
    void everyRowComposedStandsAtThePointItWasComposedFor() {
        List<String> missed = new ArrayList<>();
        forEachComposedRow((behavior, point, row) -> {
            if (!met(MODEL + example(behavior, row), point)) {
                missed.add(point + " -> " + row);
            }
        });

        assertEquals(List.of(), missed,
                "a container built to come to a total reads back as that total, which is the one"
                        + " promise every realization here is under");
    }

    /**
     * A total no one element can carry is met by several.
     *
     * <p>The half of the question that is not arithmetic. Every element of {@code ls} is capped at
     * ten and the line is at a hundred, so a container of one is a container the rules refuse — and
     * the count is chosen against what they leave rather than fixed at the fewest the container may
     * hold.
     */
    @Test
    void aTotalNoOneElementCanCarryIsMetBySeveral() {
        List<String> rows = new ArrayList<>();
        forEachComposedRow((behavior, point, row) -> {
            if (behavior.equals("needingSeveral") && point.endsWith(" ON")) {
                rows.add(row);
            }
        });

        assertEquals(1, rows.size(), () -> "the ON point of the total is composed for once: " + rows);
        assertEquals(10, rows.getFirst().split("Capped", -1).length - 1,
                () -> "a hundred is ten elements of ten and no fewer, since ten is the most one of"
                        + " them may be: " + rows.getFirst());
    }

    /**
     * A container the record it sits in counts is filled to that count.
     *
     * <p>What the elements may be is one rule and how many of them there are is another, and the
     * second is written where the ledger is rather than on the list's own type. A reading that knew
     * only {@code List<Item>} would offer one line and have it refused.
     */
    @Test
    void aContainerTheRecordCountsIsFilledToWhatItCounts() {
        List<String> rows = new ArrayList<>();
        forEachComposedRow((behavior, point, row) -> {
            if (behavior.equals("aContainerTheRecordCounts") && point.endsWith(" ON")) {
                rows.add(row);
            }
        });

        assertEquals(1, rows.size(), () -> "the ON point of the total is composed for once: " + rows);
        assertEquals(2, rows.getFirst().split("Item", -1).length - 1,
                () -> "the ledger holds two lines at the fewest, so the container built to reach the"
                        + " total holds two: " + rows.getFirst());
    }

    /**
     * A total under a dense run held away from a value is reached all the same.
     *
     * <p>An element is more than nought and there is no least value it may be: between two decimals
     * the order names nothing next. So where an element starts is a value the range holds and not
     * its floor, and a total under that start is reached by moving down from it — which is the same
     * rule the whole numbers above are under, and not a case beside it.
     */
    @Test
    void aTotalUnderADenseRunHeldAwayFromAValueIsReached() {
        assertEquals(List.of("([Money(0.5m)])"),
                rowsAt("overADenseRunHeldAwayFromNought", " ON"),
                "nothing names the first decimal above nought, and the total is a decimal above it");
    }

    /**
     * A total below where its elements start is reached by moving them down.
     *
     * <p>Nothing floors an {@code Int}, so where an element starts is a value inside the run and not
     * the least one there is — there is no least one. A decomposition that only moved elements up
     * from where they started reached no total under it, and a list of whole numbers coming to less
     * than nothing is a row anybody writes in a line.
     */
    @Test
    void aTotalBelowWhereItsElementsStartIsReached() {
        assertEquals(List.of("([-1])"), rowsAt("aTotalBelowWhereItsElementsStart", " ON"),
                "one element carries it, and it is under where an unbounded element starts");
    }

    /**
     * A total the one-sided split cannot reach is reached by sharing it.
     *
     * <p>Every element of {@code Pair} may be nought to ten and may not be four, and the line is at
     * four: a container that puts the whole of the total on one element carries a four whatever the
     * count, and a container that shares it does not. So a decomposition is one shape of several and
     * the shapes are what the rules the elements are under tell apart.
     */
    @Test
    void aTotalTheOneSidedSplitCannotReachIsShared() {
        assertEquals(List.of("(Pair { xs = [NotFour(2), NotFour(2)] })"),
                rowsAt("aTotalTheOneSidedSplitCannotReach", " ON"),
                "the shared shape is what the rule leaves, and the massed one is not");
    }

    /**
     * Where none of the shapes offered is a row, the point is left owed and said to be unfinished.
     *
     * <p>Every element of {@code Two} may be nought to ten and may not be three, four or seven, and
     * the two of them are asked to come to seven. Neither shape this offers is a row — the whole of
     * it on one element is a seven, and half each is a three and a four — and {@code [2, 5]} is one,
     * which an author writes as readily as any other.
     *
     * <p><b>So what is said is that the search stopped, and not that every row was refused.</b> The
     * second is the sentence a reader may act on (ADR-0091), and a walk that made two of the many
     * decompositions has established nothing of the kind. This is the one place the difference is
     * visible from outside: the counts here are fixed at two, so no budget over counts is what
     * leaves something unmade.
     */
    @Test
    void whereNoShapeOfferedIsARowTheSearchSaysItStopped() {
        List<String> said = new ArrayList<>();
        for (BorderAssessment border : lines(MODEL, "noShapeOfferedReachesIt")) {
            if (!border.label().contains("List.sum")) {
                continue;
            }
            ItemAssessment at = border.items().get(PointRole.ON);
            if (at instanceof ItemAssessment.Owed owed
                    && owed.attempt() instanceof ItemAssessment.Attempt.Unresolved why) {
                said.add(why.why().reason().toString());
            }
        }

        assertEquals(List.of("SEARCH_LIMIT"), said,
                "two of the decompositions were made and the rest were not, so what a reader is"
                        + " told is that this stopped");
        assertEquals(List.of(), otherThanTheAnswer(MODEL + "\nexample noShapeOfferedReachesIt\n"
                        + "    | (Two { xs = [Awkward(2), Awkward(5)] }) -> " + WHATEVER + "\n"),
                "and the row an author writes for it is one the model holds, which is why the other"
                        + " sentence would have been a lie");
    }

    /** The rows composed at the points of one behavior whose names end this way. */
    private static List<String> rowsAt(String behavior, String role) {
        List<String> rows = new ArrayList<>();
        forEachComposedRow((of, point, row) -> {
            if (of.equals(behavior) && point.endsWith(role)) {
                rows.add(row);
            }
        });
        return rows;
    }

    /** What each claim is applied to: the behavior, one of its points, and the row composed at it. */
    private interface OfAComposedRow {
        void check(String behavior, String point, String row);
    }

    private static void forEachComposedRow(OfAComposedRow held) {
        for (String behavior : ON_A_TOTAL) {
            forEachPoint(behavior, (point, item) -> {
                if (item instanceof ItemAssessment.Owed owed
                        && owed.attempt() instanceof ItemAssessment.Attempt.Built built) {
                    held.check(behavior, point, written(built.row()));
                }
            });
        }
    }

    /**
     * Every point of every line drawn on a total, and of no other line.
     *
     * <p>The rules the elements are under draw lines of their own — a floor on an amount is a border
     * at that amount — and those are somebody else's points. Walked as well, this would be asking
     * for a row at a point the rules exclude and reading the exclusion as this having composed
     * none.
     */
    private static void forEachPoint(String behavior,
                                     java.util.function.BiConsumer<String, ItemAssessment> at) {
        for (BorderAssessment border : lines(MODEL, behavior)) {
            if (border.label().contains("List.sum")) {
                border.items().forEach(
                        (role, item) -> at.accept(border.label() + " " + role, item));
            }
        }
    }

    /** A composed row's inputs, as an example line writes them. */
    private static String written(Generator.GeneratedRow row) {
        return "(" + String.join(", ",
                row.inputs().stream().map(FixtureTemplate::text).toList()) + ")";
    }

    private static String example(String behavior, String row) {
        return "\nexample " + behavior + "\n    | " + row + " -> " + WHATEVER + "\n";
    }

    /** Whether the point is met, read off the item rather than out of a report's text. */
    private static boolean met(String source, String point) {
        for (String behavior : ON_A_TOTAL) {
            for (BorderAssessment border : lines(source, behavior)) {
                for (Map.Entry<PointRole, ItemAssessment> each : border.items().entrySet()) {
                    // Named by the line and the role together, so a point of the element's own
                    // border is not read as the total's.

                    if (point.equals(border.label() + " " + each.getKey())) {
                        return each.getValue() instanceof ItemAssessment.Owed owed
                                && owed.hasRowWitness();
                    }
                }
            }
        }
        return false;
    }

    /** What the compiler says about a model, less the one thing an invented answer causes. */
    private static List<String> otherThanTheAnswer(String source) {
        Compilation compilation = measured(source);
        List<String> said = new ArrayList<>();
        for (Map.Entry<SourceId, List<Located>> each : compilation.diagnostics().entrySet()) {
            for (Located found : each.getValue()) {
                if (!THE_ANSWER_DISAGREES.equals(found.diagnostic().code())) {
                    said.add(found.diagnostic().code());
                }
            }
        }
        return said;
    }

    private static List<BorderAssessment> lines(String source, String behavior) {
        Map<String, List<BorderAssessment>> read =
                Adequacy.readingsOf(measured(source).db(), MODULE);
        assertNotNull(read, () -> "the model under test compiles: " + source);
        List<BorderAssessment> lines = read.get(behavior);
        assertNotNull(lines, () -> behavior + " was measured: " + source);
        return lines;
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
