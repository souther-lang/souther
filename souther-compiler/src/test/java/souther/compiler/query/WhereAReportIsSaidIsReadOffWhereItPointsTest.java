package souther.compiler.query;


import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Three things can say which file a report is about, and they are asked in one order. This states
 * that order, so it is a contract rather than whatever the implementation happens to do.
 *
 * <p>A key says which input was asked about. A position says where the caret sits — and the line
 * under the caret is quoted out of the file the report is filed under, so where the two disagree,
 * answering with the key's shows a reader a line they did not write. That is the whole of issue
 * #309: a question asked about a module whose rows were written in an attached {@code examples for}
 * file could only answer with the module's own file.
 *
 * <p>So the position comes first, and a report that belongs somewhere other than where its caret
 * sits says so itself. That is what {@link Report.Delivery} is for, and why it comes before both.
 */
class WhereAReportIsSaidIsReadOffWhereItPointsTest {

    /** A report pointing at line 3 of {@code positionsFile}, found by a key naming {@code keysFile}. */
    private static Db.Found found(String positionsFile, String keysFile, Report.Delivery delivery) {
        Diagnostic d = Diagnostic.uncoded("diag.hint.label")
                .at(new SourcePos(3, 3, positionsFile), 4).build();
        return new Db.Found("m", keysFile, Report.saidAt(d, delivery));
    }

    @Test
    void anExplicitDeliverySourceOverridesThePrimaryPosition() {
        Db.Found f = found("rows.sou", "model.sou", Report.Delivery.at("said.sou"));

        assertEquals("said.sou", f.claimedSourceId(),
                "a report that knows where it belongs is not overruled by where its caret sits");
    }

    @Test
    void aPrimaryPositionOverridesTheSourceTheQuestionWasAskedAbout() {
        Db.Found f = found("rows.sou", "model.sou", Report.Delivery.BY_KEY);

        assertEquals("rows.sou", f.claimedSourceId(),
                "the line under the caret is quoted from here, so this is the file");
    }

    @Test
    void theQuestionsSourceAnswersWhenThePositionNamesNone() {
        Db.Found f = found(null, "model.sou", Report.Delivery.BY_KEY);

        assertEquals("model.sou", f.claimedSourceId(),
                "a synthesized position says nothing, so what asked the question answers");
    }

    @Test
    void nothingSaysWhenNeitherDoes() {
        Db.Found f = found(null, null, Report.Delivery.BY_KEY);

        assertEquals(null, f.claimedSourceId(),
                "the module's own source is the last word, and only a caller holding the layout "
                        + "can apply it");
    }
}
