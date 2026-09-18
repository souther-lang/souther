package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A body this image has none of is a reading nobody made, and not one that met nothing.
 *
 * <p>What criterion a behavior is measured against is read off its meetings: a body that brings
 * decisions together is held to those, and one that brings none together is held to the space of
 * its positions. A body nobody read is neither, and saying it met nothing states something about
 * the model that no reading established — that this behavior is held to the neighbouring technique.
 *
 * <p>The three are what {@code CombinationCriterion} has and why it has them. Held here over a
 * model, because what a switch is total over is javac's business and what a model produces is not.
 */
class ABodyNobodyReadIsNotABodyThatMeetsNowhereTest {

    /**
     * The module whose implementation is refused, so a caller of it may not be run.
     *
     * <p>{@code %s} is what it constructs: refused, and the caller's body goes unread; accepted,
     * and the same body is read. The two readings below differ in that and in nothing else.
     */
    private static final String DOWN = """
            module probe.down exposing ( Seat, twice )

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(%s)
            """;

    /**
     * A body with decisions that meet, which this image has none of, beside one it has.
     *
     * <p>{@code omitted} forks on its input and guards on another, so its decisions meet and a
     * reading of it would answer with interactions. It also calls an implementation the module it
     * imports could not make, so it is not in this image. What it is measured against must be
     * neither of the two a reading answers with.
     */
    private static final String UP = """
            module probe.up

            import probe.down ( Seat, twice )

            data Small
            data Large
            data Size = Small | Large

            data Ok = { n: Int }
            data No

            behavior omitted : (size: Size, n: Int) -> Ok | No
                constructs Ok
            let omitted (size, n) = {
                guard n > 10 else No
                match size with
                    | Small -> Ok { n = twice(n).value }
                    | Large -> Ok { n = n }
            }

            behavior apart : (n: Int) -> Int
            let apart (n) = n

            example apart
                | "one" : (1) -> 1
            """;

    private static Compilation measured() {
        return measured("0");
    }

    private static Compilation measured(String constructs) {
        Compilation compilation =
                Compilation.ofSources(List.of(DOWN.formatted(constructs), UP), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /**
     * The model is the one this is about: the body is in the whole check and not in the image.
     *
     * <p>Written out because everything below rests on it. A model where the body is in both, or in
     * neither, reaches a different state and would answer these the same way for another reason.
     */
    @Test
    void theBodyIsInTheWholeCheckAndNotInWhatMayBeRun() {
        Compilation measured = measured();

        assertTrue(measured.db().ask(new Bodies.Checked("probe.up")).value()
                        .behaviorBodies().containsKey("omitted"),
                "the module's own bodies check, which is what makes this more than a stopped check");
        assertFalse(measured.db().ask(new Bodies.Observable("probe.up")).value()
                        .behaviorBodies().containsKey("omitted"),
                "and the implementation it reaches was not made, so this image has no body for it");
    }

    /** So nothing answers what its decisions meet, and the criterion is neither of the two. */
    @Test
    void nothingAnswersWhatItsDecisionsMeet() {
        Compilation measured = measured();

        assertFalse(measured.db().ask(new Adequacy.Interacts("probe.up")).value()
                        .containsKey("omitted"),
                "a reading nobody made is no entry, not an entry that met nothing");
        assertTrue(measured.db().ask(new Adequacy.Interacts("probe.up")).value()
                        .containsKey("apart"),
                "and the behavior beside it, whose body is here, is answered for");
    }

    /**
     * And the two surfaces say the same thing about it.
     *
     * <p>One of them used to test for the reading that answers with interactions and take the other
     * way for everything else, so a behavior nothing read a body of was printed as held to the
     * space of its positions on one page and left alone on the other.
     */
    @Test
    void neitherSurfaceHoldsItToTheSpaceOfItsPositions() {
        Compilation measured = measured();
        AdequacyReport report = AdequacyReport.of(measured);
        SourceRendering rendering = SourceRendering.namedByIdentity(measured.texts());

        String human = report.human(rendering);
        assertFalse(human.contains("combination"),
                () -> "nothing read this body, so no page says what it is held to combine: "
                        + human);
        assertEquals(List.of(), report.findings().stream()
                        .filter(each -> each.about()
                                instanceof About.ACombinationOfTwoClassesNoRowIsIn)
                        .map(each -> each.subject().toString())
                        .toList(),
                "and nothing is owed a row in a space nobody held this behavior to");
    }

    /**
     * And a generation goes on offering what it can for the behavior.
     *
     * <p>The other half of not answering for the meetings. What could not be read is one part of
     * this body, and the rows the positions of it already ask for are work an author can do — a
     * generation that gave the whole behavior up because one part of it cannot be searched would
     * take back what another part had already found.
     */
    @Test
    void aGenerationGoesOnOfferingWhatItCan() {
        Compilation measured = measured();

        String block = GeneratedRows.of(measured, null, null,
                SourceRendering.namedByIdentity(measured.texts())).text();

        assertTrue(block.contains("example omitted"),
                () -> "the positions of this body still ask for rows: " + block);
    }

    /**
     * And neither measure concludes over the rules it never read.
     *
     * <p>One rule of a body makes both: {@code guard n > 10} divides the position it is about and
     * draws a line at the number it names. Read, both measures close over it; unread, a closed
     * partition would say the model divides that position no further and a closed border would say
     * no rule of the model draws a line — which is the proof {@code NoRuleDrawsALine} takes.
     *
     * <p>Held as the difference between the two readings rather than as a state written out here.
     * What has to hold is that the absence of a reading is not the absence of the rules.
     */
    @Test
    void neitherMeasureConcludesOverRulesItNeverRead() {
        String read = String.valueOf(measured("1").db()
                .ask(new Adequacy.Dividing("probe.up", "omitted")).value());
        String unread = String.valueOf(measured("0").db()
                .ask(new Adequacy.Dividing("probe.up", "omitted")).value());

        assertTrue(read.contains("partitionClosure=PartitionClosed")
                        && read.contains("borderClosure=BorderClosed"),
                () -> "read, both measures run out: " + read);
        assertTrue(read.contains("id=omitted/n, term=n, classes=[Partition"),
                () -> "and the guard divides the position it is about: " + read);

        assertTrue(unread.contains("partitionClosure=PartitionBodyNotRead")
                        && unread.contains("borderClosure=BorderBodyNotRead"),
                () -> "unread, neither concludes: " + unread);
        assertFalse(unread.contains("id=omitted/n, term=n, classes=[Partition"),
                () -> "the guard is not recovered from a body nobody read: " + unread);
    }

    /**
     * And no position of it is said to be one the model divides no way.
     *
     * <p>The other half of not concluding. A measure that came to nothing says so about the measure;
     * what a report sends an author to is the position, and there the same reading would have said
     * that the model draws no distinction at {@code n} — over a {@code guard} two tokens away that
     * nothing read.
     *
     * <p>The pair is what says it. Read, {@code n} is measured and is no longer a position anything
     * is undivided about; unread, it is one, and what is held is which sentence it gets.
     */
    @Test
    void noPositionOfABodyNobodyReadIsSaidToBeUndividedByTheModel() {
        List<UndividedPosition> read = undividedOf(measured("1"));
        List<UndividedPosition> unread = undividedOf(measured("0"));

        assertEquals(List.of(), read.stream().map(each -> each.at().toString())
                        .filter(each -> each.equals("n")).toList(),
                () -> "read, the guard divides this position and nothing is undivided at it: "
                        + read);
        assertEquals(List.of("n"), unread.stream().map(each -> each.at().toString())
                        .filter(each -> each.equals("n")).toList(),
                () -> "unread, nothing measures it: " + unread);
        assertEquals(List.of(), unread.stream()
                        .filter(each -> each.why() instanceof UndividedPosition.Why.Absent)
                        .map(each -> each.at().toString())
                        .toList(),
                "a position of a body nobody read is not a position the model divides no way");
    }

    /** What the partition measure of {@code omitted} is left undivided at. */
    private static List<UndividedPosition> undividedOf(Compilation measured) {
        return measured.db().ask(new Adequacy.Dividing("probe.up", "omitted")).value()
                .geometry().undivided();
    }
}
