package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.DeclaringCode;
import souther.compiler.diag.Placement;
import souther.compiler.diag.SourcePos;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.source.SourceId;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Moving a report to where a reader can be sent does not change what it is about.
 *
 * <p>A position says which text it is in and whose code it carries, separately. A body spliced into
 * a module's published text while that module was being read back is in {@code m}'s text and is
 * {@code p}'s code, and a report from inside it is about {@code p}. Moving the caret to the import
 * line that reached {@code m} is a change to where the reader is sent and is not a change to what
 * the code is.
 *
 * <p>Which is easy to get wrong in one direction only. The move is made by the walk that knows which
 * module it was reading, so the module is to hand and the report's own answer has to be preferred
 * over it — and rebuilding the answer from the module is the inference this whole change removes:
 * that code found in a module's text is that module's code.
 *
 * <p>Held here rather than on a compile, because a compile cannot get into this state: a module whose
 * invariant reaches a construction in another module's helper is refused when it is built, so the
 * middle module never reaches a reader. The rule is what is checked, not a route to it.
 */
class AMovedReportKeepsWhereItsCodeIsWrittenTest {

    private static final SourceProvenance THE_TEXT = new SourceProvenance.APublishedModule("mid");
    private static final SourceProvenance THE_CODE =
            new SourceProvenance.APublishedModule("up", "up.atLeastZero");

    @Test
    void aReportFromASplicedBodyIsAboutTheBodyAndNotTheTextItWasSplicedInto() {
        SourcePos spliced = Placement.whatAModulePublished(THE_TEXT).at(4, 20)
                .standingInFor(new DeclaringCode(THE_CODE));

        assertEquals(THE_CODE, Compilation.whereTheCodeIs(spliced, "mid"),
                "the report is about the body that was copied in, and the module it was found in is"
                        + " where it was found");
    }

    /** And a report in a module's own published text is about that module, which is the same rule
     *  reading the same answer — the position carries it either way. */
    @Test
    void aReportFromAModulesOwnTextIsAboutThatModule() {
        assertEquals(THE_TEXT,
                Compilation.whereTheCodeIs(Placement.whatAModulePublished(THE_TEXT).at(4, 20), "mid"),
                "code of a text's own is written where that text is");
    }

    /**
     * A report with no position at all takes the module it was filed under.
     *
     * <p>The one case where the module is the answer, and it is the answer because there is nothing
     * else: no position, so nothing carrying where the code is. That is what makes it a fallback
     * rather than a second authority.
     */
    @Test
    void aReportWithNoPositionTakesTheModuleItWasFiledUnder() {
        assertEquals("mid", Compilation.whereTheCodeIs(null, "mid").module(),
                "nothing to read it off, and the module is what is known about the report");
    }

    /** A place a reader holds is not moved at all, so nothing here applies to it — the walk asks
     *  first, and this says what it would answer if it did not. */
    @Test
    void aPlaceTheReaderHoldsIsNotSomethingThisIsAskedAbout() {
        assertEquals("mid",
                Compilation.whereTheCodeIs(
                        Placement.aFileOfThisCompile(new SourceId("down.sou")).at(2, 1), "mid")
                        .module(),
                "a report already pointing at a file the reader holds is not moved, and asked out of"
                        + " turn this falls back the same way a placeless one does");
    }
}
