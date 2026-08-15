package souther.compiler.diag;

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
 * <p>Built one way, from a region ({@link #of}), so the classification is made once. Every reader is
 * then a switch over two arms and gains a compile error the day a third is added — where before each
 * of them read {@code sourceId == null} and answered a different question with it: the renderer read
 * it as "the diagnostic's file", the clause reader as "drop this", the adequacy warning as "drop
 * this", and moving a caret as "drop this".
 *
 * <p>{@link Unavailable} is not the absence of a place. It carries where the code came from, which
 * is what a reader is told instead of being pointed somewhere — and is the fact a drop threw away.
 */
public sealed interface DiagnosticPlace {

    /**
     * The stretch a reader is sent to, and empty where there is nothing to send one to.
     *
     * <p>A projection over the two arms and not a second answer: a caller reading this has said
     * which case it is in by the time it has a region in its hands, and which source that region is
     * in is part of the region. It is here rather than on {@link LabeledRegion} so that holding a
     * label is not the same as holding a place — a label says what is wrong, and where that is is
     * this.
     */
    default java.util.Optional<Region> pointsAt() {
        return switch (this) {
            case InSource in -> java.util.Optional.of(in.region());
            case Unavailable _ -> java.util.Optional.empty();
        };
    }

    /**
     * A stretch of {@code source} a reader can be sent to.
     *
     * <p>Both a place a source of this compile was read for and a copy of code from out of sight
     * that was given the caller's place to be read against. The two differ in what the coordinate
     * says about itself ({@link WrittenAt}), and not in whether there is somewhere to send a reader.
     */
    record InSource(String source, Region region) implements DiagnosticPlace {

        public InSource {
            Objects.requireNonNull(source, "a place a reader is sent to names its source");
            Objects.requireNonNull(region, "a place a reader is sent to is a stretch of it");
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
     * <p>Two questions, asked in this order and neither answered off the other. Whether there is a
     * file to quote is whether the region names a source. What the numbers stand for is the
     * coordinate's own provenance. A copy spliced into a caller answers yes to the first and stands
     * in all the same, which is why the first cannot be read off the second.
     *
     * @throws NotAPlace where there is no region, where it has no ends, or where it names no source
     *         and its coordinate says the code is written at it. The last is a position somebody made
     *         by hand and did not place, and it used to mean "read it in the diagnostic's file" — a
     *         reading that made this defect possible and is gone
     * @throws NotOnePlace where the ends were read from two sources
     */
    static DiagnosticPlace of(Region region) {
        if (region == null) {
            throw new NotAPlace("a label is about a region and was given none");
        }
        SourcePos start = region.start();
        SourcePos end = region.end();
        if (start == null || end == null) {
            throw new NotAPlace("a region a label is about has two ends: " + region);
        }
        if (!Objects.equals(start.sourceId(), end.sourceId())) {
            throw new NotOnePlace(start.sourceId(), end.sourceId());
        }
        if (start.sourceId() != null) {
            return new InSource(start.sourceId(), region);
        }
        if (Citation.of(start) instanceof Citation.OutOfSight out) {
            return new Unavailable(out.provenance());
        }
        throw new NotAPlace(
                "a region naming no source is a place nobody settled, and a report may not settle it"
                        + " from where it happens to be shown: " + region);
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

        NotOnePlace(String start, String end) {
            super("a region runs from " + start + " to " + end
                    + ", which is not one place in one source");
        }
    }
}
