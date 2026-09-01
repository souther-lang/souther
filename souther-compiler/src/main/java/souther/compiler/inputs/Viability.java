package souther.compiler.inputs;

import souther.compiler.check.Emptiness;

import java.util.ArrayList;
import java.util.List;
import java.util.function.Function;

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

    /**
     * What two things a value has at once come to.
     *
     * <p>A conjunction, and the connective is the whole of the difference from {@link #oneOf}: a row
     * has every one of these, so one of them standing nowhere is the row standing nowhere, and every
     * one of them has to be possible for the row to be. What is not known about one of them cannot
     * hide what another was shown — so a proof wins over an unread, and an unread wins over nothing
     * having been shown.
     *
     * <p>Written here rather than at each fold. The two connectives read alike and mean opposite
     * things, and a caller working out for itself which of three answers to keep would sooner or
     * later keep the one that reads like the other fold's.
     */
    default Viability with(Viability other) {
        if (this instanceof ProvedImpossible) {
            return this;
        }
        if (other instanceof ProvedImpossible) {
            return other;
        }
        return this instanceof NotRead ? this : other;
    }

    /**
     * What the alternatives of one choice come to.
     *
     * <p>A disjunction. A value is one of these, so one that may stand is the whole answer, and what
     * proves there is none is every one of them at once — which is why the proofs are taken
     * together rather than one being picked to speak for the rest. An alternative nothing is known
     * about leaves the choice unproved however many of the others are refused.
     *
     * @param alternatives what became of each, in the order the model writes them
     * @param proof        what the refusals come to where every one of them is refused, which is
     *                     whatever kind of choice this is
     */
    static Viability oneOf(List<Viability> alternatives,
                           Function<List<Emptiness>, Emptiness> proof) {
        List<Emptiness> refused = new ArrayList<>();
        boolean unread = false;
        for (Viability each : alternatives) {
            switch (each) {
                case MayStand _ -> {
                    return each;
                }
                case ProvedImpossible it -> refused.add(it.why());
                case NotRead _ -> unread = true;
            }
        }
        return unread ? new NotRead() : new ProvedImpossible(proof.apply(refused));
    }

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
