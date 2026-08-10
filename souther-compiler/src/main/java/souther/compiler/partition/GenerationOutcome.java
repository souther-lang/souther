package souther.compiler.partition;

import java.util.List;

/**
 * What the generator can do about one gap a build refuses.
 *
 * <p>Every such gap has one of these, and a gap with none is a gap an author is told nothing about
 * while the block above it reads as though it filled everything.
 *
 * <p>Which of the three it is, is a question about strategies and not about searches. A strategy that
 * takes a gap of this kind and composed nothing is {@link CannotGenerate}; a gap no strategy takes is
 * {@link NotSupported}. Whether anything was tried belongs in the reason. Reading the kind off a
 * search — nothing enumerated, so nothing supported — would settle what the generator is able to do
 * from what one run happened to touch, and the answer would move with the model rather than with the
 * compiler.
 *
 * <p>So a gap moves between the three as strategies are written, and a strategy that gains a form it
 * can read moves gaps from {@link NotSupported} to one of the others. That is the whole of what these
 * say.
 */
public sealed interface GenerationOutcome {

    /** A strategy applies, and it composed rows. */
    record Generated(List<Generator.GeneratedRow> candidates) implements GenerationOutcome {

        public Generated {
            candidates = List.copyOf(candidates);
        }
    }

    /**
     * A strategy applies, and it composed nothing.
     *
     * <p>Never a claim that nothing can be written. What the attempt established is carried whole, and
     * saying more than it is the thing this type exists to prevent.
     */
    record CannotGenerate(Generator.UnresolvedCombination why) implements GenerationOutcome {}

    /** No strategy takes a gap of this kind, or the form this one would need. */
    record NotSupported(Reason reason) implements GenerationOutcome {

        /**
         * Why nothing takes it — a fact about which strategies are written, not about the model.
         *
         * <p>Each of these is a strategy that could exist and does not. None of them says the gap
         * cannot be met, and none is read as evidence about the model.
         */
        public enum Reason {

            /** Nothing composes an input for the sake of the path it would take through a body. */
            NO_STRATEGY_FOR_AN_ARM("nothing here composes an input for the arm it would reach"),

            /** Nothing searches for an input by the output it produces. */
            NO_STRATEGY_FOR_AN_OUTPUT_CASE(
                    "nothing here searches for an input by the case it would answer with"),

            /** The position the case belongs to is not one any axis was derived at. */
            NO_AXIS_AT_THIS_POSITION("no axis was derived at the position this case belongs to");

            private final String said;

            Reason(String said) {
                this.said = said;
            }

            /** The reason as a report writes it. */
            public String said() {
                return said;
            }
        }
    }
}
