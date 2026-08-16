package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;

/**
 * Where a report points, as a finished answer: a stretch of a source a reader can be sent to, or
 * nothing to point at and something to say instead.
 *
 * <p>Complete on its own. A place that had to be combined with the diagnostic it ends up in before
 * it meant anything is not a place — it is an expression waiting for a context, and the context it
 * waited for is what made a label about a published module's clause read as a line of the caller's
 * file. So there is no arm for "wherever this is put": whoever builds one of these knows which
 * source it is in, and a caller that does not know has not finished answering.
 *
 * <p>A region is classified one way, through {@link #of}, so the reading of a region is made once.
 * A site holding no region builds an {@link Unavailable} outright, having nothing to classify — what
 * it has is where the code came from. Every reader is a switch over the two arms and gains a compile
 * error the day a third is added, where before each of them read {@code sourceId == null} and
 * answered a different question with it: the renderer read it as "the diagnostic's file", the clause
 * reader as "drop this", the adequacy warning as "drop this", and moving a caret as "drop this".
 *
 * <p>{@link Unavailable} is not the absence of a place. It carries where the code came from, which
 * is what a reader is told instead of being pointed somewhere — and is the fact a drop threw away.
 *
 * <p>No accessor spans the two arms. One answering "the region, if there is one" would let a reader
 * write {@code place.pointsAt().flatMap(Optional::stream)} and never see the other case — which is
 * {@code CitableRegion.of} again, under a name that reads like a convenience. {@link Citation} says
 * the same of itself and for the same reason: a reader that wants the region says which case it is
 * in first, and having said so has seen that the other exists.
 */
public sealed interface DiagnosticPlace {

    /**
     * A stretch of source a reader can be sent to.
     *
     * <p>Both a place a source of this compile was read for and a copy of code from out of sight
     * that was given the caller's place to be read against. The two differ in what the position says
     * about itself ({@link Placement}), and not in whether there is somewhere to send a reader.
     *
     * <p>One component, and the source is read off it. A source held beside a region that carries
     * one is two values for one fact with nothing keeping them the same — which is the shape this
     * whole change is about, and it does not stop being that shape because the type is new. Held as
     * a pair, {@code new InSource("A", Region.point(new SourcePos(1, 1, "B")))} would be a legal
     * value, and the rule that they agree would be a habit of one factory rather than something the
     * type says.
     *
     * <p>So what the factory checks, this checks. Reaching {@link #of} is how one of these is made
     * and not the reason one of them is sound.
     */
    record InSource(Region region) implements DiagnosticPlace {

        public InSource {
            heldToOnePlace(region);
            if (!(region.start().quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds)) {
                throw new NotAPlace("a place a reader is sent to names the source it is in: "
                        + region);
            }
        }

        /** The source this is in, which is the source the region was read from. */
        public SourceId source() {
            return ((QuotedFrom.ASourceThisCompileHolds) region.start().quotedFrom()).source();
        }
    }

    /**
     * Code this compile holds no file for, so there is nothing to quote and nothing to put a caret
     * under. {@code provenance} is what a report says in place of pointing.
     */
    record Unavailable(SourceProvenance provenance) implements DiagnosticPlace {

        public Unavailable {
            Objects.requireNonNull(provenance, "code out of sight came from somewhere");
        }
    }

    /**
     * Where {@code region} is, classified once.
     *
     * <p>Off the citation the region's start projects, which is where those two questions are
     * already answered together. A copy spliced into a caller is somewhere a reader can be sent and
     * stands in for code elsewhere at once, and that is one arm rather than a pair of answers this
     * would have to combine.
     *
     * @throws NotAPlace where there is no region, where it has no ends, or where the text it is in
     *         is one this compilation cannot name while saying the code is written there. That is a
     *         position somebody made by hand and did not place, and it used to mean "read it in the
     *         diagnostic's file" — a reading that made this defect possible and is gone
     * @throws NotOnePlace where the ends are in two places
     */
    static DiagnosticPlace of(Region region) {
        heldToOnePlace(region);
        return switch (Citation.of(region.start())) {
            case Citation.Written _, Citation.Reached _ -> new InSource(region);
            case Citation.OutOfSight out -> new Unavailable(out.provenance());
            case Citation.Unplaced _ -> throw new NotAPlace(
                    "a region naming no source is a place nobody settled, and a report may not"
                            + " settle it from where it happens to be shown: " + region);
        };
    }

    /**
     * A region that is no place: none at all, one with an end missing, or one nobody placed.
     *
     * <p>Marked like {@link NotOnePlace}, and for the reason that type gives. What raises one of
     * these runs inside an analysis that falls open, and a refusal that arrived as an ordinary
     * {@link IllegalArgumentException} would be swallowed there — turning a label this could not
     * place into a whole subject reported as having nothing wrong with it, which is what a subject
     * that passed looks like. Dropping one label was the old behaviour and was already the defect;
     * dropping the analysis around it is worse.
     */
    final class NotAPlace extends IllegalArgumentException implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotAPlace(String message) {
            super(message);
        }
    }

    /**
     * Refuses a region that is not one place before anything is asked of it.
     *
     * <p>The whole of where a position is, and not just the file. A region whose ends are in two
     * places is a place that is two places, and a placement is what says which place one end is in —
     * so this is one comparison rather than a file test and a provenance test that could be kept in
     * step by hand. Read off the start alone, the second end's answer would go unrecorded: a region
     * running from a copy of {@code A} to a copy of {@code B} would come back as a report about
     * {@code A}, and nothing anywhere would say otherwise.
     *
     * <p>Held here rather than on {@link Region}, which is a pair of coordinates and is built by
     * every pass; this is where a pair is asked to be a place. Measured before it was written: no
     * region in the compiler's own corpus has ends that disagree about provenance.
     */
    private static void heldToOnePlace(Region region) {
        if (region == null) {
            throw new NotAPlace("a label is about a region and was given none");
        }
        SourcePos start = region.start();
        SourcePos end = region.end();
        if (start == null || end == null) {
            throw new NotAPlace("a region a label is about has two ends: " + region);
        }
        if (!start.placement().equals(end.placement())) {
            throw new NotOnePlace("a region runs from " + start.placement() + " to "
                    + end.placement() + ", which is not one place");
        }
    }

    /**
     * A region whose ends were read from two sources.
     *
     * <p>Its own type because a check that would see one swallows what it throws: an analysis that
     * fell over leaves the run-time check standing, which is the right answer for a shape the walk
     * has no rule for and the wrong one here. What this says is that the compiler built a place that
     * is not a place — and swallowed, it comes out as a behavior with nothing to report, the same
     * thing a behavior whose invariants all discharge comes out as.
     *
     * <p>Here rather than beside the caller that used to raise it, because this is where a region
     * becomes a place and a region that is two places has no place to become.
     */
    final class NotOnePlace extends IllegalArgumentException
            implements TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotOnePlace(String message) {
            super(message);
        }
    }
}
