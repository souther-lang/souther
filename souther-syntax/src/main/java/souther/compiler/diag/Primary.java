package souther.compiler.diag;

import java.util.Objects;

/**
 * What a diagnostic points at, as a finished answer.
 *
 * <p>Four arms because a {@link Citation} tells apart four things a report can be in, and this is
 * the boundary they were being flattened at. A region arrived here unclassified and a report with
 * nothing to point at arrived as {@code null}, so downstream had to work out which of them it was
 * holding — from the module the report was filed under, from whether a resolver answered, from
 * whether a caller had thought to pass a source. Those are three different guesses at one question
 * this now answers.
 *
 * <p>Which arm a region is in is settled once, in {@link #at}, off the citation its start projects.
 * A site with nothing to point at says so outright, having nothing to classify.
 *
 * <h2>What each arm asks of whoever shows the report</h2>
 *
 * <p>Nothing, except one. {@link InSource} carries the source it is in, so a surface reads it and
 * asks the caller for nothing. {@link Unavailable} carries where the code came from, which is what
 * a reader is told instead of being sent anywhere. {@link Nowhere} points at nothing and says
 * nothing about code: the report is about a file or about the compile, and which file it is listed
 * under is the caller's answer and not a place ({@code ReportContext}).
 *
 * <p>{@link InAnUnnamedText} is the one that asks. Its line and column are real and which text they
 * are of was never given, so a surface can send a reader there only if it says which text it is
 * showing. That is the whole of what a told source was ever for, and it is now asked for by exactly
 * the arm that needs it rather than handed to every report and read by whichever reader felt like
 * it.
 */
public sealed interface Primary {

    /**
     * A stretch of a source this compilation holds, which a reader can be sent to.
     *
     * <p>The place answers for its own source ({@link DiagnosticPlace.InSource#source()}), so
     * nothing beside it does. Both a position read from one of this compile's files and a body
     * spliced into one of them are here: they differ in where the code is written, which
     * {@link Diagnostic#whereItsCodeIsWritten()} answers, and not in whether there is somewhere to
     * send a reader.
     */
    record InSource(DiagnosticPlace.InSource place) implements Primary {

        public InSource {
            Objects.requireNonNull(place, "a report pointing into a source names it");
        }
    }

    /**
     * A stretch of a text this compilation cannot name — an editor's unsaved buffer, a snippet a
     * caller parsed.
     *
     * <p>The numbers are real and the file is not this value's to say. A surface showing one of
     * these says which text it is reading, and a surface that does not may not guess: quoting
     * whatever sits at those numbers in whichever file was to hand is the defect this whole family
     * of types exists to stop.
     */
    record InAnUnnamedText(UnnamedRegion where) implements Primary {

        public InAnUnnamedText {
            Objects.requireNonNull(where, "a report about a stretch of a text has one");
        }
    }

    /**
     * Nowhere to point, and the code is written in {@code from}.
     *
     * <p>What a report about code inside a module's published text has: the position it was found at
     * is a line of a text no reader holds, so there is nothing to offer, and which module wrote that
     * code is known and is what a reader is told instead.
     */
    record Unavailable(SourceProvenance from) implements Primary {

        public Unavailable {
            Objects.requireNonNull(from, "code out of sight came from somewhere");
        }
    }

    /**
     * Nothing to point at, and nothing to say about where code is either.
     *
     * <p>Not a report that lost its place: one that never was about a stretch of text. A module
     * declared here and also on the path is wrong about neither line; the compiler running out of
     * room is not a fact about the source at all. Which file such a report is listed under is a real
     * question and is not this one — it is answered where the report is shown, because only a caller
     * holding the files can answer it.
     */
    record Nowhere() implements Primary {

        /** The one of these there is. It carries nothing, so two of them are the same one. */
        public static final Nowhere IT = new Nowhere();
    }

    /**
     * Where {@code region} is, classified once.
     *
     * <p>Off the citation the region's start projects, which is where the two questions a placement
     * is the product of are already answered together. The same reading {@link DiagnosticPlace#of}
     * makes of a label's region, with one difference: a label that cannot be placed is refused,
     * because a label is offered to a reader or is not written, and a primary that cannot be placed
     * is the report itself and has to be carried.
     *
     * @throws DiagnosticPlace.NotAPlace where there is no region or it has no ends
     * @throws DiagnosticPlace.NotOnePlace where the ends are in two places
     */
    static Primary at(Region region) {
        OnePlace.heldTo(region);
        return switch (Citation.of(region.start())) {
            case Citation.Written _, Citation.Reached _ ->
                    new InSource(new DiagnosticPlace.InSource(region));
            case Citation.Unplaced _, Citation.UnplacedElsewhere _ ->
                    new InAnUnnamedText(new UnnamedRegion(region));
            // A position inside a module's published text is a line of a text nobody holds. There is
            // nothing to point at, and what is known is which module wrote the code — so the region
            // is not carried on to be read as a place by whoever forgets to ask.
            case Citation.OutOfSight out -> new Unavailable(out.provenance());
        };
    }
}
