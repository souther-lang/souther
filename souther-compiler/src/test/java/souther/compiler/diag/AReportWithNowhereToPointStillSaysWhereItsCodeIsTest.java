package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.source.SourceId;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a report with nowhere to point tells a reader, on every surface that shows it.
 *
 * <p>A citation tells five states apart and a diagnostic's primary now carries the one that has no
 * place and does know where the code is. Carrying it is only half: a value nothing reads is a value
 * nobody has, and the surfaces read the primary's <em>region</em> — which such a report has none of.
 * So the terminal said the sentence with no account of why there was no caret, and the JSON a build
 * reads said nothing at all.
 *
 * <p>Both of those are the drop this whole change is about, arriving at the last boundary: a fact the
 * compiler knows, thrown away, and reconstructed downstream from whatever is to hand.
 */
class AReportWithNowhereToPointStillSaysWhereItsCodeIsTest {

    private static final SourceProvenance THE_CODE =
            new SourceProvenance.APublishedModule("lib.rule", "lib.rule.atLeast");

    private static Diagnostic nowhereToPoint() {
        return Diagnostic.atCodeWrittenOutOfSight(THE_CODE)
                .say(new ModuleMessage.CannotReadAFieldOnASum("x", "S"))
                .build();
    }

    /** The sentence a person is shown says where the code is, the way a label with nothing to point
     *  at says it — one wording for the same situation, whichever part of a report is in it. */
    @Test
    void theSentenceAPersonReadsSaysWhereTheCodeIs() {
        String body = DiagnosticRenderer.body(nowhereToPoint(), Locale.ENGLISH);

        assertTrue(body.contains("lib.rule.atLeast"),
                () -> "a report with no caret says which code it is about: " + body);
    }

    /** And what a build reads says it as a value rather than inside a sentence, in the words this
     *  document already uses for code out of sight. */
    @Test
    void whatABuildReadsSaysItAsAValue() {
        String json = new JsonRenderer().render(
                new Located(nowhereToPoint(), new SourceId("app.sou")),
                _ -> null, Locale.ENGLISH);

        assertTrue(json.contains("\"writtenAt\""),
                () -> "a tool reads where the code is rather than parsing the message: " + json);
        assertTrue(json.contains("lib.rule.atLeast"), () -> json);
        assertFalse(json.contains("\"region\""),
                () -> "and there is no region, because there is nowhere to point: " + json);
    }

    /**
     * Moving such a report somewhere a reader can be sent does not re-decide what it is about.
     *
     * <p>A caller says where the code is because a report with nothing pointed at has no answer to
     * read; one that has an answer is not asking. Handing it a different one is somebody working it
     * out again from what was to hand, which is the whole shape of this defect.
     */
    @Test
    void movingItSomewhereReadableDoesNotRedecideWhatItIsAbout() {
        assertThrows(Diagnostic.MovedSomewhereElsesCode.class,
                () -> nowhereToPoint().reachedFrom(
                        java.util.List.of(new SourcePos(2, 1, new SourceId("app.sou"))),
                        new SourceProvenance.APublishedModule("lib.other"),
                        new ModuleMessage.ItIsReachedFromHereToo()));
    }

    /** Moved with what it says, it becomes a report a reader can be sent to, still about the same
     *  code. */
    @Test
    void movedWithWhatItSaysItPointsSomewhereAndIsAboutTheSameCode() {
        Diagnostic moved = nowhereToPoint().reachedFrom(
                java.util.List.of(new SourcePos(2, 1, new SourceId("app.sou"))), THE_CODE,
                new ModuleMessage.ItIsReachedFromHereToo());

        Citation.Reached reached =
                (Citation.Reached) Citation.of(moved.region().start());
        assertEquals(THE_CODE, reached.provenance(), "the same code");
        assertTrue(reached.at().isIn(new SourceId("app.sou")), "somewhere the reader holds");
    }
}
