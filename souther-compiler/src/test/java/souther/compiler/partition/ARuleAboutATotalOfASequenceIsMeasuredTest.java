package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule about what a sequence's values come to is measured, and no line falls where they are read
 * from.
 *
 * <p>The two together are the whole of it. A model whose central rule is a threshold on a total had
 * its border reported as one no line was derived for — the sentence a model that states no rule at
 * all gets — and the fix must not be a line at the element position instead: two lines of sixty and
 * forty are on the boundary of a hundred as surely as one of a hundred is, so a class there would be
 * about a rule the model does not state and an author could not tell it from one they wrote.
 *
 * <p>The shapes are here together because what separates them is what this had to answer. A total of
 * a bare list is one operation over a location; a total of a mapped list is the same operation over
 * values a walk answered; a count of the same list is a third number of the same place. Each was a
 * different half of the reading, and a change that gains one by losing another passes none of these.
 */
class ARuleAboutATotalOfASequenceIsMeasuredTest {

    private static final String MODULE = "example.claims";

    private static final String MODEL = """
            module example.claims

            data Amount = Int
                invariant value >= 0

            data Item = { amount: Amount, free: Bool }

            data Needed
            data NotNeeded
            data Verdict = Needed | NotNeeded

            behavior overABareList : (ns: List<Int>) -> Verdict
            let overABareList (ns) =
                if List.sum(ns) >= 100000 then Needed else NotNeeded

            behavior overDecimals : (ds: List<Decimal>) -> Verdict
            let overDecimals (ds) =
                if List.sum(ds) >= 100.5m then Needed else NotNeeded

            behavior overAProjection : (lines: List<Item>) -> Verdict
            let overAProjection (lines) =
                if List.sum(List.map(line -> line.amount.value, lines)) >= 100000
                    then Needed else NotNeeded

            let total (lines: List<Item>): Int =
                List.sum(List.map(line -> line.amount.value, lines))

            behavior throughAHelper : (lines: List<Item>) -> Verdict
            let throughAHelper (lines) =
                if total(lines) >= 100000 then Needed else NotNeeded

            behavior throughALocalName : (lines: List<Item>) -> Verdict
            let throughALocalName (lines) = {
                let amounts = List.map(line -> line.amount.value, lines)
                if List.sum(amounts) >= 100000 then Needed else NotNeeded
            }

            data TooSmall
            behavior underAGuard : (lines: List<Item>) -> Needed | TooSmall
            let underAGuard (lines) = {
                guard total(lines) > 0 else TooSmall
                Needed
            }

            behavior overABranchingProjection : (lines: List<Item>) -> Verdict
            let overABranchingProjection (lines) =
                if List.sum(List.map(line -> if line.free then 0 else line.amount.value, lines))
                        >= 100000 then Needed else NotNeeded

            behavior counting : (lines: List<Item>) -> Verdict
            let counting (lines) =
                if List.length(lines) >= 3 then Needed else NotNeeded

            behavior aTotalAndACount : (ns: List<Int>) -> Verdict
            let aTotalAndACount (ns) =
                if List.sum(ns) >= 100000 && List.length(ns) >= 3
                    then Needed else NotNeeded
            """;

    /** A total of a list a behavior takes is a number of that location, like a count of it. */
    @Test
    void aTotalOfABareListIsMeasured() {
        assertEquals(List.of("overABareList/List.sum(ns)"), axesOf("overABareList"));
        assertEquals(List.of("overDecimals/List.sum(ds)"), axesOf("overDecimals"),
                "the elements decide which number it answers, and decimals answer one too");
    }

    /**
     * A name in the middle is a name, and the rule either side of it is one rule.
     *
     * <p>The mapped list bound before it is totalled, which is how a model of any size writes this
     * and how the model that started all of it does. What a name stands for is the reading of the
     * input's answer, so the walk is met through it — read off the expression as written instead,
     * this shape and the one above are two different rules, and which one an author wrote is
     * whether they gave the list a name.
     */
    @Test
    void aNameBetweenTheWalkAndTheTotalChangesNothing() {
        assertEquals(pointsOn("overAProjection"), pointsOn("throughALocalName"),
                "the same points are owed against the same total whether or not the mapped list was"
                        + " given a name");
    }

    /**
     * A total of what a walk answered is measured at the number, and the place its values are read
     * from keeps no class.
     */
    @Test
    void aTotalOfAProjectionIsMeasuredAndTheElementKeepsNoClass() {
        for (String behavior : List.of("overAProjection", "throughAHelper", "underAGuard",
                "throughALocalName")) {
            // The place the values are read from and not every place: a `Bool` beside them is
            // divided by its own type, which no rule about a total has anything to do with. What
            // must not be here is a class of the numbers the total was added up from.
            assertTrue(axesOf(behavior).stream().noneMatch(each -> each.contains("amount")),
                    () -> behavior + ": a total divides no position, and least of all the one its"
                            + " values are read from: " + axesOf(behavior));
            assertTrue(reasonsOf(behavior).contains(UndividedPosition.Reason.RULE_ABOUT_A_RUN),
                    behavior + ": and the rule is named as one about what the values come to");
        }
    }

    /**
     * The line is on the total, with the four points a border owes standing against it.
     *
     * <p>Read off what was measured and not out of the report's text. What a point is owed is one
     * question and what became of the search for a row at it is another, and the sentence a report
     * prints is about the second: a point a row was composed for is no longer written down as one
     * nothing was, so a test reading the text would say the point had gone.
     */
    @Test
    void theLineIsOnTheTotalAndItsPointsAreOwed() {
        assertEquals(List.of("List.sum(lines[*].amount) = 100000 ON",
                        "List.sum(lines[*].amount) = 100000 OFF",
                        "List.sum(lines[*].amount) = 100000 IN",
                        "List.sum(lines[*].amount) = 100000 OUT"),
                pointsOn("overAProjection"),
                "a border on a total owes the four points every border owes");
    }

    /** The points of the total's own line, in the order a border names them. */
    private static List<String> pointsOn(String behavior) {
        Compilation compilation = measured();
        List<String> out = new java.util.ArrayList<>();
        for (souther.compiler.query.BorderAssessment border
                : souther.compiler.query.Adequacy.readingsOf(compilation.db(), MODULE)
                        .get(behavior)) {
            if (border.label().contains("List.sum")) {
                border.items().forEach((role, _) -> out.add(border.label() + " " + role));
            }
        }
        return out;
    }

    /**
     * A closure whose answer is no place of its element is still explicitly unread.
     *
     * <p>The half this cannot prove is which position the answer stands at, and the rule is reported
     * as one written about a value made from what is there — the same sentence it got before any of
     * this, because nothing about that shape has changed.
     */
    @Test
    void aBranchingProjectionStaysUnread() {
        assertTrue(reasonsOf("overABranchingProjection")
                        .contains(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                "what the branch answers is not read out of the element, so the rule is one this"
                        + " could not follow rather than one about a run");
        assertTrue(axesOf("overABranchingProjection").stream()
                        .noneMatch(each -> each.contains("List.sum")),
                "and no total is measured");
    }

    /** A count of the same list is a number of it, and unaffected. */
    @Test
    void aCountOfTheSameListIsStillItsOwnNumber() {
        assertTrue(axesOf("counting").contains("counting/List.length(lines)"),
                () -> "a count is a number of the location, whatever else is measured beside it: "
                        + axesOf("counting"));
    }

    /**
     * A total and a count of one list are two numbers at one location, and both are measured.
     *
     * <p>The shape a position carrying two axes is, reached here for the first time by a rule an
     * author would write: before a total could be read, the two numbers of one list were one number
     * and a count.
     */
    @Test
    void aTotalAndACountOfOneListAreTwoMeasures() {
        assertEquals(List.of("aTotalAndACount/List.sum(ns)", "aTotalAndACount/List.length(ns)"),
                axesOf("aTotalAndACount"));
    }

    private static List<String> axesOf(String behavior) {
        return evidence().get(behavior).axes().stream()
                .map(each -> each.at().toString()).toList();
    }

    private static List<UndividedPosition.Reason> reasonsOf(String behavior) {
        return evidence().get(behavior).notRead().stream()
                .map(PartitionEvidence.NotRead::reason).toList();
    }

    private static Map<String, PartitionEvidence> evidence() {
        Compilation compilation = measured();
        return compilation.db().ask(new Adequacy.Coverage(MODULE)).value();
    }

    private static String report() {
        Compilation compilation = measured();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
