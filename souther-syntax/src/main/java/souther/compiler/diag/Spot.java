package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;
import java.util.Optional;

/**
 * One place a reader can be sent to, with the text to quote it from settled.
 *
 * <p>Two arms, and the difference is which value answers for the text. {@link InSource} reads it off
 * the place, which carries it ({@link DiagnosticPlace.InSource#source()}). {@link InTextBeingRead}
 * is handed it, because its region is in a text this compilation cannot name and the surface showing
 * the report is the only thing that knows which text that is.
 *
 * <p>So a source identity is never held beside something that already answers for one. That pairing
 * is what this class used to be — a told source and a region, taken apart again by every renderer,
 * so a pair that disagreed was a marker put in one file with its line quoted from another. It is
 * gone rather than checked: the arm whose region answers does not carry a second answer, and the arm
 * that carries one has a region that answers nothing ({@link UnnamedRegion}).
 *
 * <p>What a spot says it is about is not here. A place is a place whether the report is about it or
 * points at it to explain something, and which of those it is belongs to the report
 * ({@link Shown}). Held here, every reader of a place had to know that a null note meant "this is
 * the primary".
 */
public sealed interface Spot {

    /** The stretch this points at. Both arms have exactly one, so asking for it skips no case. */
    Region region();

    /** A place in a source this compilation holds. */
    record InSource(DiagnosticPlace.InSource place) implements Spot {

        public InSource {
            Objects.requireNonNull(place, "a place in a source names the source");
        }

        @Override
        public Region region() {
            return place.region();
        }
    }

    /** A place in the text the surface says it is reading. */
    record InTextBeingRead(TextBeingRead text, UnnamedRegion where) implements Spot {

        public InTextBeingRead {
            Objects.requireNonNull(text, "a place in a text the caller is reading names that text");
            Objects.requireNonNull(where, "a place is a stretch of it");
        }

        @Override
        public Region region() {
            return where.region();
        }
    }

    /**
     * Whether two spots are known to be in one text.
     *
     * <p>Answered from identities, and only where both have one. A surface asks this to decide
     * whether to write a file name over a place it is about to quote, and "cannot tell" has to come
     * back as "not known to be one": naming the file of a place that turns out to be the same one
     * costs a reader a line they did not need, and leaving it off a place in another file leaves
     * them a line and column with no file to read them in.
     *
     * <p>Across the arms as readily as within them. A document an editor publishes by name and a
     * report parsed out of that same document's unsaved text are one text, and the day
     * {@link TextBeingRead} carries an identity for a text handed over, more pairs answer yes here
     * and nowhere else.
     */
    static boolean knownToBeOneText(Spot one, Spot other) {
        Optional<SourceId> here = identityOf(one);
        Optional<SourceId> there = identityOf(other);
        return here.isPresent() && here.equals(there);
    }

    /** Whether this spot is known to be in the text {@code source} names — the same question,
     *  asked of a text a caller has an identity for and no spot in. */
    static boolean knownToBeIn(Spot spot, SourceId source) {
        return source != null && identityOf(spot).filter(source::equals).isPresent();
    }

    /**
     * The identity of the text a spot is in, where there is one to compare.
     *
     * <p>Private, and the only reader is the comparison above. Published, it would be the accessor
     * spanning the arms that this package refuses everywhere else: a caller would read it, find an
     * empty answer for a text handed over, and put the report wherever it was being shown.
     */
    private static Optional<SourceId> identityOf(Spot spot) {
        return switch (spot) {
            case InSource in -> Optional.of(in.place().source());
            case InTextBeingRead(TextBeingRead text, UnnamedRegion _) -> text.identity();
        };
    }
}
