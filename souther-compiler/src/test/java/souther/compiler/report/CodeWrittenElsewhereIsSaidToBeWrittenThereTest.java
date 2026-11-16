package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.SourceLayout;
import souther.compiler.diag.Citation;
import souther.compiler.diag.DeclaringCode;
import souther.compiler.diag.Placement;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;
import souther.compiler.publish.PublishedAt;
import souther.compiler.source.SourceId;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A clause of a line that says where code is written says it by what the citation of the code is.
 *
 * <p>Code written in another declaration than where this compile met it has a citation naming where
 * it is and the call it was reached through. "Written at" before that reads the call as the place
 * the code is, which is what a citation that separates the two exists to prevent.
 */
class CodeWrittenElsewhereIsSaidToBeWrittenThereTest {

    private static final Page PAGE = new Page(
            SourceRendering.namedByIdentity(SourceLayouts.NONE), Locale.ENGLISH);

    private static final SourceId DECLARED_IN = new SourceId("a.sou");

    @Test
    void codeOfAModuleThatWasPublishedIsSaidToBeWrittenInIt() {
        Citation outOfSight = Citation.of(Placement.whatAModulePublished(
                new SourceProvenance.APublishedModule("lib.a")).at(1, 0));

        Message said = AdequacyReport.whereWritten(outOfSight, PAGE, DECLARED_IN);

        assertEquals(new ReportMessage.InAPlace("`lib.a`"), said);
        assertEquals(", written in `lib.a`", PAGE.say(said));
    }

    private static final SourceId FILE = new SourceId("app.sou");

    /** The call a body was spliced into, in a file this compile holds, standing in for code that is
     *  written in {@code List.filter}. */
    private static SourcePos theCall() {
        return Placement.aFileOfThisCompile(FILE).at(0, 0, 0).standingInFor(
                new DeclaringCode(new SourceProvenance.TheStandardLibrary("std.list"))
                        .reachedBy("List.filter"));
    }

    @Test
    void codeReachedThroughACallIsSaidToBeWrittenWhereItIsAndReachedAtTheCall() {
        SourceLayout layout = SourceLayout.of("module m\n", FILE);
        Page page = new Page(SourceRendering.namedByIdentity(_ -> layout), Locale.ENGLISH);
        Citation reached = Citation.of(theCall());

        assertInstanceOf(Citation.Reached.class, reached);
        Message said = AdequacyReport.whereWritten(reached, page, FILE);

        assertEquals(", written in `List.filter`, reached at 1:1", page.say(said),
                "the call is not said to be where the code is written");
    }

    @Test
    void theDocumentKeepsTheCallAsThePlaceAndSaysWhereTheCodeIsWrittenBesideIt() {
        SourcePos call = theCall();

        PublishedAt published = PublishedAt.of(Citation.of(call)).orElseThrow();

        assertEquals(call, published.at(), "the place is the call");
        assertEquals(new PublishedAt.Where.OutOfSight("List.filter"), published.writtenAt(),
                "and the code is said to be elsewhere");
        assertEquals(Citation.outOfSightFields("List.filter"), published.writtenAt().fields());
    }

    @Test
    void codeWrittenWhereItWasMetIsSaidToBeWrittenAt() {
        Citation written = Citation.of(Placement.aFileOfThisCompile(DECLARED_IN).at(1, 0));

        assertInstanceOf(Citation.Written.class, written);
        assertInstanceOf(ReportMessage.AtAPlace.class,
                AdequacyReport.whereWritten(written, PAGE, DECLARED_IN));
    }
}
