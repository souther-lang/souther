package souther.compiler.diag;

import java.util.Objects;

/**
 * What came of asking a report's primary for a place a reader can be sent to.
 *
 * <p>Four answers, because there are three ways the answer can be no and they are not the same
 * thing. A report about a module rather than a stretch of text has no place to offer and nothing to
 * say instead; one about code out of sight has nowhere to point and does have something to say; and
 * one in a text nobody named is a place the surface could have shown had it said which text it is
 * reading. The first two are the report's state. The third is the surface's, and it is the one that
 * is somebody's mistake rather than a fact about the code.
 *
 * <p>Which is why it is a value rather than an empty {@link java.util.Optional}. A missing display
 * context that came back as absence would read as "this report points nowhere", so a surface would
 * show the sentence and nobody would learn that a caller had not said which text it was showing.
 * Nothing is thrown for it: an editor holding an unsaved buffer is the ordinary reason a report is
 * in a text with no name, and taking a session down over a caller that did not pass one is worse
 * than showing the sentence with no caret.
 */
public sealed interface SpotResolution {

    /** There is a place, and here it is. */
    record Found(Spot spot) implements SpotResolution {

        public Found {
            Objects.requireNonNull(spot, "a resolution that found a place has one");
        }
    }

    /** The report is not about a stretch of text. Which file it is listed under is a separate
     *  question, answered by {@link ReportContext#filedUnder()}. */
    record NoPrimary() implements SpotResolution {

        /** The one of these there is. */
        public static final NoPrimary IT = new NoPrimary();
    }

    /** There is nowhere to point, and this is where the code is written — what a reader is told
     *  instead of being sent anywhere. */
    record CodeUnavailable(SourceProvenance from) implements SpotResolution {

        public CodeUnavailable {
            Objects.requireNonNull(from, "code out of sight came from somewhere");
        }
    }

    /**
     * There is a stretch of text and the surface did not say which text it is reading.
     *
     * <p>The line and the column are real and are carried, so what happened is legible: this is a
     * caller that had a place to show and did not name the text it was showing it from. Nothing
     * downstream may put those numbers against a text it guessed at, which is the whole of what
     * telling this apart is for.
     */
    record TextWasNotProvided(UnnamedRegion where) implements SpotResolution {

        public TextWasNotProvided {
            Objects.requireNonNull(where, "a place nobody named is still a place");
        }
    }

    /**
     * What {@code primary} comes to, given what the surface says it is reading.
     *
     * <p>The one place the two are put together. Every surface asked its own version of this
     * question before — of a told source, of whether a resolver answered, of whether a region was
     * null — and each answered a different one of the four with the same silence.
     */
    static SpotResolution of(Primary primary, ReportContext context) {
        return switch (primary) {
            case Primary.InSource(DiagnosticPlace.InSource place) ->
                    new Found(new Spot.InSource(place));
            case Primary.InAnUnnamedText(UnnamedRegion where) ->
                    context.textBeingRead()
                            .<SpotResolution>map(text ->
                                    new Found(new Spot.InTextBeingRead(text, where)))
                            .orElseGet(() -> new TextWasNotProvided(where));
            case Primary.Unavailable(SourceProvenance from) -> new CodeUnavailable(from);
            case Primary.Nowhere _ -> NoPrimary.IT;
        };
    }
}
