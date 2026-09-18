package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
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

    /** The module whose implementation is refused, so a caller of it may not be run. */
    private static final String DOWN = """
            module probe.down exposing ( Seat, twice )

            data Seat = Int
                invariant value >= 1 && value <= 300

            behavior twice : (n: Int) -> Seat
            let twice (n) = mint(n)

            behavior mint : (n: Int) -> Seat
                constructs Seat
            let mint (n) = Seat(0)
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
        Compilation compilation = Compilation.ofSources(List.of(DOWN, UP), ModulePath.EMPTY);
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
}
