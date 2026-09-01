package souther.compiler.inputs;

import souther.compiler.check.Emptiness;

/**
 * What is known about whether a value stands somewhere.
 *
 * <p><b>One arm proves and the other two do not, and that asymmetry is the whole of it.</b> A proof
 * of emptiness may be built out of {@link ProvedImpossible} and out of nothing else: where every
 * alternative of a sum carries one, the sum has no value; where any of them carries anything else,
 * nothing has been shown. {@link MayStand} and {@link NotRead} are one answer to that calculus —
 * not shown impossible — and differ only in what a report may say about why.
 *
 * <p>Which is why the third is written down rather than left as an absence. A case this walk never
 * entered has no root, no reading and nothing to look up, and every one of those is a shape some
 * later reader takes for "there is nothing there". Given a name of its own, taking it for a proof is
 * something that has to be typed out.
 *
 * <p>The same asymmetry {@code Cardinality} holds: a count carries its proof or it carries nothing,
 * and a count nothing has shown to be none is not a claim that a value exists.
 */
sealed interface Viability {

    /** Nothing showed that nothing stands here. Not a claim that something does. */
    record MayStand() implements Viability {}

    /** Nothing stands here, and this is what showed it. */
    record ProvedImpossible(Emptiness why) implements Viability {

        public ProvedImpossible {
            if (why == null) {
                throw new IllegalArgumentException("what is impossible is impossible for a reason");
            }
        }
    }

    /**
     * This reading did not go there, so nothing is known either way.
     *
     * <p>Where it stopped is not carried. Nothing asks it yet, and a place picked out of however
     * many alternatives went unread would be chosen by the order they were walked in rather than by
     * anything the model says — which is the shape of answer this type exists to keep out. A reader
     * that needs the place is a reader that says which of them it wants.
     */
    record NotRead() implements Viability {}
}
