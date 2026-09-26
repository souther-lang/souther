package souther.compiler.regex;

import java.util.List;

/**
 * A pattern as its reader holds it before the anchors are placed.
 *
 * <p>The one shape here {@link PatternMeaning} does not have is {@link Anchor}. What an anchor comes
 * to is settled by where it stands among the rest of the pattern, which is not known until the
 * whole of it is read; so the reader keeps it as written, {@link Anchors} works out what it comes
 * to, and what leaves the reader holds none. Everything else is already its meaning and is held as
 * one ({@link Meant}), so there is one vocabulary for sets of symbols and the empty string, and it
 * is the one that goes on.
 *
 * <p>Private to this package. Nothing outside the reader has a use for an anchor that has not been
 * placed, and one that reached an output would be a second place asked what it means.
 */
sealed interface WrittenPattern {

    /** A part with no anchor in it, as what it means. */
    record Meant(PatternMeaning meaning) implements WrittenPattern {}

    /**
     * A place a match must be at, written {@code ^} or {@code $}.
     *
     * @param end whether it is {@code $} rather than {@code ^}
     */
    record Anchor(boolean end) implements WrittenPattern {}

    /** One after another. */
    record InTurn(List<WrittenPattern> parts) implements WrittenPattern {

        public InTurn {
            parts = List.copyOf(parts);
        }
    }

    /** Any one of them. */
    record EitherOf(List<WrittenPattern> arms) implements WrittenPattern {

        public EitherOf {
            arms = List.copyOf(arms);
        }
    }

    /** The same thing some number of times over, with the bounds {@link PatternMeaning.Repeated}
     *  takes. */
    record Repeated(WrittenPattern what, int least, int most) implements WrittenPattern {}
}
