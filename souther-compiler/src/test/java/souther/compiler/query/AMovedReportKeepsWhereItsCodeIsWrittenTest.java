package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Citation;
import souther.compiler.diag.DeclaringCode;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Placement;
import souther.compiler.diag.Primary;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.source.SourceId;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * Moving a report to where a reader can be sent does not change what it is about.
 *
 * <p>A position says which text it is in and whose code it carries, separately. A body spliced into
 * a module's published text while that module was being read back is in {@code mid}'s text and is
 * {@code up}'s code, and a report from inside it is about {@code up}. Moving the caret to the import
 * line that reached {@code mid} is a change to where the reader is sent and is not a change to what
 * the code is.
 *
 * <p>Which is easy to get wrong in one direction only. The move is made by the walk that knows which
 * module it was reading, so the module is to hand and the report's own answer has to be preferred
 * over it — and rebuilding the answer from the module is the inference this whole change removes:
 * that code found in a module's text is that module's code.
 *
 * <p>Asked of the diagnostic rather than of a position, because that is where the answer was being
 * lost. A citation tells five states apart and a primary region could hold two, so a report with
 * nowhere to point arrived here as a report with nothing at all, and the module was the only thing
 * left to answer from. The states are what the diagnostic carries now, and this reads them.
 */
class AMovedReportKeepsWhereItsCodeIsWrittenTest {

    private static final SourceProvenance THE_TEXT = new SourceProvenance.APublishedModule("mid");
    private static final SourceProvenance THE_CODE =
            new SourceProvenance.APublishedModule("up", "up.atLeastZero");

    /** Something for a report to say, which is not what any of this is about. */
    private static Diagnostic.Builder saying(Diagnostic.Builder built) {
        return built.say(new ModuleMessage.CannotReadAFieldOnASum("x", "S"));
    }

    /**
     * A report about a body spliced into a module's published text is about the body.
     *
     * <p>There is nowhere to point — the position is a line of a text no reader holds — so the
     * report says so and says which module wrote the code. Both halves are needed: without the
     * first it would offer a place nobody has, and without the second the move would have to invent
     * one.
     */
    @Test
    void aReportFromASplicedBodyIsAboutTheBodyAndNotTheTextItWasSplicedInto() {
        Diagnostic said = saying(Diagnostic.atCodeWrittenOutOfSight(THE_CODE)).build();

        assertEquals(THE_CODE, Compilation.whatToMove(said, "mid"),
                "the report is about the body that was copied in, and the module it was found in is"
                        + " where it was found");
    }

    /** And one in a module's own published text is about that module, which is the same rule reading
     *  the same answer — the report carries it either way. */
    @Test
    void aReportFromAModulesOwnTextIsAboutThatModule() {
        Diagnostic said = saying(Diagnostic.atCodeWrittenOutOfSight(THE_TEXT)).build();

        assertEquals(THE_TEXT, Compilation.whatToMove(said, "mid"),
                "code of a text's own is written where that text is");
    }

    /** A position still inside a published text, never turned into a place, says the same thing —
     *  the citation answers whether it was reached from anywhere, and this one was not. */
    @Test
    void aReportLeftAtAPositionInsideAPublishedTextIsAboutThatText() {
        Diagnostic said = saying(Diagnostic.at(Placement.whatAModulePublished(THE_TEXT).at(4, 20)))
                .build();

        assertEquals(THE_TEXT, Compilation.whatToMove(said, "mid"),
                "a position in a module's own text points at a line nobody holds");
    }

    /**
     * A report with nothing pointed at takes the module it was filed under.
     *
     * <p>The one case where the module is the answer, and it is the answer because there is nothing
     * else. That is what makes it a fallback rather than a second authority.
     */
    @Test
    void aReportWithNothingPointedAtTakesTheModuleItWasFiledUnder() {
        Diagnostic said = saying(Diagnostic.at((SourcePos) null)).build();

        assertEquals("mid", Compilation.whatToMove(said, "mid").module(),
                "nothing to read it off, and the module is what is known about the report");
    }

    /** A place the reader holds is left where it is. */
    @Test
    void aReportPointingAtAFileTheReaderHoldsIsNotMoved() {
        Diagnostic said = saying(Diagnostic.at(
                Placement.aFileOfThisCompile(new SourceId("down.sou")).at(2, 1))).build();

        assertNull(Compilation.whatToMove(said, "mid"),
                "a reader can already be sent there");
    }

    /**
     * And so is one in a text this compilation cannot name.
     *
     * <p>Its position is one whoever handed the text over can use, and nothing about it says where
     * its code came from — so moving it would mean answering that from the module, which is the
     * inference this is about. Whether such a position is a place at all is the open question about
     * a primary region, and this leaves it open rather than deciding it by writing a provenance.
     */
    @Test
    void aReportInATextThisCompilationCannotNameIsNotMovedEither() {
        Diagnostic said = saying(Diagnostic.at(Placement.aTextWithNoIdentity().at(3, 3))).build();

        assertNull(Compilation.whatToMove(said, "mid"),
                "nothing here says where the code came from, and the module is not an answer to that");
    }

    /**
     * And the warning that finds such code says so, rather than saying nothing.
     *
     * <p>The other half of this boundary. A finding holds a citation, which tells five states apart,
     * and the diagnostic it becomes used to hold a region or nothing — so a finding with nowhere to
     * point arrived as a report with nothing at all, and the module was all that was left to answer
     * from. This is the step that has to keep it, and the step above is the one that reads it.
     */
    @Test
    void aWarningAboutCodeItCannotShowSaysWhereThatCodeIs() {
        Citation cited = Citation.of(Placement.whatAModulePublished(THE_TEXT).at(4, 20)
                .standingInFor(new DeclaringCode(THE_CODE)));

        Diagnostic said = saying(Adequacy.Warnings.pointedAt(cited)).build();

        assertEquals(new Primary.Unavailable(THE_CODE), said.primary(),
                "nowhere to point, and which module wrote the code — a warning that dropped the"
                        + " second would leave the move to work it out from somewhere else");
        assertEquals(THE_CODE, Compilation.whatToMove(said, "mid"),
                "and the move keeps it");
    }

    /** A body spliced into such a text does say where its code came from, and is moved with it. */
    @Test
    void aBodySplicedIntoSuchATextIsMovedWithWhatItSays() {
        SourcePos spliced = Placement.aTextWithNoIdentity().at(3, 3)
                .standingInFor(new DeclaringCode(THE_CODE));
        Diagnostic said = saying(Diagnostic.at(spliced)).build();

        assertNull(Compilation.whatToMove(said, "mid"),
                "a position in a text this compilation cannot name is left where it is, whatever it"
                        + " carries — what is missing is a place, and that is the open question");
    }
}
