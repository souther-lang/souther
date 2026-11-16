package souther.compiler.report;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.Citation;
import souther.compiler.diag.Placement;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.Message;
import souther.compiler.diag.msg.ReportMessage;
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

    @Test
    void codeWrittenWhereItWasMetIsSaidToBeWrittenAt() {
        Citation written = Citation.of(Placement.aFileOfThisCompile(DECLARED_IN).at(1, 0));

        assertInstanceOf(Citation.Written.class, written);
        assertInstanceOf(ReportMessage.AtAPlace.class,
                AdequacyReport.whereWritten(written, PAGE, DECLARED_IN));
    }
}
