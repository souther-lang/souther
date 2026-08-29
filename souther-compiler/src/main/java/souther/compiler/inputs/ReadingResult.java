package souther.compiler.inputs;

import java.util.List;

/**
 * What crossing a position's distinctions with the rules reaching it came to, as the reading found
 * it.
 *
 * <p>The fact, before any policy is applied to it. What a measure is owed is a separate question
 * with an answer of its own ({@link ObligationDomain}), and the two are held apart so that a
 * decision about what to do with an awkward reading is written in one place instead of being
 * rediscovered by each reader — which is how the same conservative fallback came to live inside the
 * producer, where nobody could see it had been applied.
 *
 * <p>{@link Complete} with nothing kept is a reading that ran to the end and found the position
 * holds no value at all. It is a fact about the model — a declaration nothing can construct — and
 * it stays written down as one here, whatever the readers currently do about it.
 */
public sealed interface ReadingResult {

    /** The distinctions the rules leave, which is what a row can be written at where the reading
     *  settles it. */
    List<Case> kept();

    /** The distinctions the rules refuse. Proven in every arm: what the rules leave is an upper
     *  bound however much of them was read. */
    List<Case> refused();

    /** Every rule reaching the position was read. */
    record Complete(List<Case> kept, List<Case> refused) implements ReadingResult {

        public Complete {
            kept = List.copyOf(kept);
            refused = List.copyOf(refused);
        }
    }

    /**
     * A rule about the position was written and this reading did not take it in.
     *
     * <p>The refusals still hold and the admissions do not. So both lists are carried and they are
     * not the same claim: {@code refused} is what the rules proved empty, and {@code kept} is what
     * this reading has no reason to remove — which a rule that went unread may yet remove.
     */
    record Partial(List<Case> kept, List<Case> refused, BlockReason.ReadingStopReason why)
            implements ReadingResult {

        public Partial {
            kept = List.copyOf(kept);
            refused = List.copyOf(refused);
            if (why == null) {
                throw new IllegalArgumentException("a partial reading knows why it is partial");
            }
        }
    }

    /**
     * Every rule about the position was read, and the reading could not hold what they say
     * together.
     *
     * <p>What {@link Partial} says about its lists holds here for a different reason: the refusals
     * still hold and the admissions do not, since what is kept is a product standing for a relation
     * two of its clauses cannot state. It carries no reason — no rule is answerable for it and what
     * would lift it is one thing — which is also what tells it from {@link Partial} at a reader.
     */
    record NotSeparated(List<Case> kept, List<Case> refused) implements ReadingResult {

        public NotSeparated {
            kept = List.copyOf(kept);
            refused = List.copyOf(refused);
        }
    }

    /**
     * Nothing about the position was read: its type could not be interpreted, or the walk never
     * reached it.
     *
     * <p>Distinct from a reading that found no rules. A position nothing is written about is
     * {@link Complete} with every distinction kept, and says so about the model; this says nothing
     * about the model at all.
     */
    record Unsupported(BlockReason.ReadingStopReason why) implements ReadingResult {

        public Unsupported {
            if (why == null) {
                throw new IllegalArgumentException(
                        "a reading supported by nothing is one that was made");
            }
        }

        @Override
        public List<Case> kept() {
            return List.of();
        }

        @Override
        public List<Case> refused() {
            return List.of();
        }
    }
}
