package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.partition.ClassOfAPosition;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An obligation every row of which reaches an {@code unreachable} nothing proves is owed and
 * undecided: not taken away, and not a gap.
 *
 * <p>Three answers kept apart. What a row is owed at is the model's, and an {@code unreachable} is a
 * statement and not a proof, so the obligation stays and the count is what it was — taken out on the
 * body's word, the one row that would show the statement wrong is the row nothing asks for. A row
 * there is refused (E1911), so the obligation is not one an author can be told to meet, and a build
 * refusing over it refuses over work nobody can do. What is left is undecided, which a strict build
 * does not refuse over and which says what it is open on.
 *
 * <p>Whole cells only. A body that answers nothing at one value of a third position and answers at
 * the other leaves a row that meets the pair, so that pair is a gap like any other.
 */
class AnObligationEveryRowOfWhichReachesAnUnreachableIsUndecidedTest {

    /** A matrix with one blank cell, which the body states is blank. */
    private static final String BLANK = """
            module example.blank

            data X
            data Y
            data A = X | Y
            data P
            data Q
            data B = P | Q

            behavior f : (a: A, b: B) -> Int

            let f (a, b) =
                match a with
                    | X -> 1
                    | Y -> match b with
                             | P -> 2
                             | Q -> unreachable "Y is never asked with Q"

            example f
                | "X P" : (X, P) -> 1
                | "X Q" : (X, Q) -> 1
                | "Y P" : (Y, P) -> 2
            """;

    /**
     * The same pair in the same position, answered with a number: a row can be written there, so
     * no row being there is a gap. Without this, a measure that stopped refusing over pairs at all
     * would pass everything below.
     */
    private static final String ANSWERED = BLANK.replace(
            "unreachable \"Y is never asked with Q\"", "3");

    /** The blank cell blank only where a third position is {@code On}. */
    private static final String HALF_BLANK = """
            module example.half

            data X
            data Y
            data A = X | Y
            data P
            data Q
            data B = P | Q
            data On
            data Off
            data C = On | Off

            behavior f : (a: A, b: B, c: C) -> Int

            let f (a, b, c) =
                match a with
                    | X -> 1
                    | Y -> match b with
                             | P -> 2
                             | Q -> match c with
                                      | On  -> unreachable "never On here"
                                      | Off -> 3

            example f
                | "X P On"  : (X, P, On) -> 1
                | "X Q Off" : (X, Q, Off) -> 1
                | "Y P Off" : (Y, P, Off) -> 2
            """;

    /** And blank whatever the third position is, every arm of it saying so for its own reason. */
    private static final String ALL_BLANK = HALF_BLANK.replace(
            "| Off -> 3", "| Off -> unreachable \"never Off here\"");

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static PartitionEvidence.PairSpace pairsOf(Compilation compilation) {
        PartitionEvidence partition = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("f");
        assertNotNull(partition, "the model under test compiles");
        return partition.pairs();
    }

    /** The finding about the combination of {@code one} with {@code other}, by class id. */
    private static Adequacy.Finding pairFinding(Compilation compilation, String one,
                                                String other) {
        return AdequacyReport.of(compilation).findings().stream()
                .filter(each -> each.about()
                        instanceof About.ACombinationOfTwoClassesNoRowIsIn(var cell)
                        && cell.classes().stream().map(ClassOfAPosition::classId)
                                .collect(Collectors.toSet()).equals(Set.of(one, other)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no finding about " + one + " with " + other
                        + " in " + AdequacyReport.of(compilation).findings()));
    }

    /** What the body's premise says, where a finding is held open on one. */
    private static List<String> premiseOf(Adequacy.Finding finding) {
        return finding.weakenedBy().causes().stream()
                .filter(Weakening.PremiseUnproven.class::isInstance)
                .map(each -> ((Weakening.PremiseUnproven) each).reasons())
                .findFirst().orElse(List.of());
    }

    private static String reportOn(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    /**
     * The pair is still counted, and nothing the body says took it out.
     *
     * <p>The arithmetic and not the two numbers apart: a pair gone from the space and from the rows
     * at once would leave a ratio that looks the same.
     */
    @Test
    void theBlankCellIsStillOneOfThePairs() {
        PartitionEvidence.PairSpace pairs = pairsOf(measured(BLANK));

        assertEquals(4, pairs.total(), "two classes against two");
        assertEquals(3, pairs.counts().covered());
    }

    /** And it is undecided on the body's premise, which is what the verdict comes to. */
    @Test
    void theBlankCellIsUndecidedOnTheBodysPremise() {
        Compilation compilation = measured(BLANK);
        Adequacy.Finding blank = pairFinding(compilation, "Y", "Q");

        assertEquals(Adequacy.Finding.Disposition.UNDECIDED, blank.disposition());
        assertEquals(List.of("Y is never asked with Q"), premiseOf(blank));
        assertEquals(AdequacyReport.AdequacyStatus.UNDETERMINED,
                AdequacyReport.of(compilation).adequacy());
    }

    /** The control: the same pair answered is a gap a row closes, and a build refuses over it. */
    @Test
    void theSamePairAnsweredIsAGap() {
        Compilation compilation = measured(ANSWERED);
        Adequacy.Finding answered = pairFinding(compilation, "Y", "Q");

        assertEquals(Adequacy.Finding.Disposition.REFUSED, answered.disposition());
        assertEquals(List.of(), premiseOf(answered));
        assertEquals(AdequacyReport.AdequacyStatus.NOT_SATISFIED,
                AdequacyReport.of(compilation).adequacy());
    }

    /**
     * The report says why, and keeps what it said about the claim.
     *
     * <p>That the claim is not proven is the claim's own line and stays; the pair line is told the
     * same premise in the words the body wrote, which is what makes "undecided" something an author
     * can act on.
     */
    @Test
    void theReportSaysWhatTheCellIsOpenOn() {
        String report = reportOn(measured(BLANK));

        assertTrue(report.contains("· undecided whether a row is in `Y` at f/a with `Q` at f/b:"
                        + " a row there reaches `unreachable` (Y is never asked with Q)"),
                report);
        assertTrue(report.contains("`Q` is declared unreachable: Y is never asked with Q, and"
                + " nothing here proves it"), report);
        assertTrue(report.contains("adequacy: undetermined"), report);
    }

    /**
     * A third position the body answers at leaves the pair a gap.
     *
     * <p>A row at {@code Y} and {@code Q} with {@code Off} beside them answers {@code 3}. Read as
     * "some row of the pair aborts" instead of "every row does", this pair would be undecided and a
     * row an author can write would go unasked for.
     */
    @Test
    void aPairTheBodyAnswersForSomewhereIsAGap() {
        Adequacy.Finding half = pairFinding(measured(HALF_BLANK), "Y", "Q");

        assertEquals(Adequacy.Finding.Disposition.REFUSED, half.disposition());
        assertEquals(List.of(), premiseOf(half));
    }

    /**
     * And where every arm under the pair aborts, the pair is undecided as a whole.
     *
     * <p>The part that answers nothing is the {@code match} on the third position, not either of
     * its arms, so the pair is covered by one part and not by putting two together. Both reasons
     * are what a run there may abort with.
     */
    @Test
    void aPairEveryArmUnderWhichAbortsIsUndecided() {
        Adequacy.Finding all = pairFinding(measured(ALL_BLANK), "Y", "Q");

        assertEquals(Adequacy.Finding.Disposition.UNDECIDED, all.disposition());
        assertEquals(List.of("never On here", "never Off here"), premiseOf(all));
    }

    /**
     * What the generator offers is what the compiler accepts.
     *
     * <p>Taken out, answered and compiled. A row at the blank cell is E1911 the moment it is
     * compiled, and so is any row the generator happened to put there while filling something else.
     * The answers written are not the body's, so each row is refused for its answer — which is a
     * row that ran and came back with one, and is what every row not at the blank cell does. That
     * there is something to take is asserted rather than assumed: a generator that offered nothing
     * would pass the rest.
     */
    @Test
    void everyRowOfferedBesideTheBlankCellCompiles() {
        // The blank cell one move from the first row: the nearest row at `P` is the blank cell
        // itself. The two charges meet, so the combinations owed are the meeting's and not the
        // pairs, and every one of them has a row — what is left is the class `P` alone, and no row
        // the offering would rather keep stands in for the one composed for it.
        String sparse = """
                module example.blank

                data X
                data Y
                data A = X | Y
                data P
                data Q
                data B = P | Q
                data On
                data Off
                data C = On | Off

                behavior f : (a: A, b: B, c: C) -> Int

                let f (a, b, c) = {
                    let left = match a with
                        | X -> match b with
                                 | P -> unreachable "X is never asked with P"
                                 | Q -> 1
                        | Y -> 2
                    let right = match c with
                        | On  -> 10
                        | Off -> 20

                    left + right
                }

                example f
                    | "X Q On"  : (X, Q, On) -> 11
                    | "X Q Off" : (X, Q, Off) -> 21
                    | "Y Q On"  : (Y, Q, On) -> 12
                    | "Y Q Off" : (Y, Q, Off) -> 22
                """;
        String offered = GeneratedRows.of(measured(sparse), "example.blank", "f",
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();

        assertFalse(offered.contains("(X, P"), offered);
        StringBuilder rows = new StringBuilder();
        for (String line : offered.lines().toList()) {
            if (!line.startsWith("//")) {
                rows.append(line).append('\n');
            }
        }
        assertTrue(rows.toString().contains("| "), () -> "the block offers rows: " + offered);
        String answered = sparse + "\n" + rows.toString().replace("<?>", "0");
        Compilation amended = Compilation.ofSource(answered, "Main");
        amended.answerEverything();
        List<String> refused = amended.db().allReports().stream()
                .filter(found -> found.report().isError())
                .map(found -> found.report().diagnostic().code()).toList();
        assertFalse(refused.contains("E1911"), () -> refused + "\n" + answered);
    }

    /** And nothing is offered at the blank cell where it is all that is left. */
    @Test
    void nothingIsOfferedAtTheBlankCell() {
        String offered = GeneratedRows.of(measured(BLANK), "example.blank", "f",
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();

        assertFalse(offered.contains("(Y, Q)"), offered);
    }
}
