package souther.compiler.reach;

import souther.compiler.types.TypeSymbol;

import java.util.List;

/**
 * How it was shown that nothing arrives.
 *
 * <p>Cut by what was shown and not by what showed it — the same rule the emptiness proofs are under.
 * A domain added to the reading writes one of these, and only a new thing to <em>say</em> earns a
 * new arm. Named after the domain that found it, every domain would be an arm, and the sentence an
 * author reads would change when an implementation did.
 *
 * <p><b>Taken apart by writing the sentences, and no other way.</b> The arms are not types anything
 * outside this package can name, so there is no {@code instanceof} to reach for and no import that
 * opens one: a reader gets at what a proof holds by handing over a {@link Words}, which has one
 * method per arm. Adding an arm is then a compile error in every reader that writes sentences —
 * which is the whole point of keeping this out of the readers that decide — rather than a silent
 * fall into whichever branch a switch happened to end with.
 */
public sealed interface Proof permits ConditionsThatCannotAllHold, EveryCaseRefused {

    /**
     * The sentences a proof can come to, one per arm.
     *
     * <p>What each is handed is what that proof holds, not the proof: a reader writing words has no
     * use for the value and every use for its parts, and passing the value would let one arm's
     * writer ask about another's.
     */
    interface Words<T> {

        /**
         * The conditions on the way here cannot all hold.
         *
         * <p>The general form: what is known is that together they leave nothing, and which of them
         * is doing it is not claimed. A smallest set that still contradicts would be a nicer
         * sentence and is a different piece of work — one this does not pretend to have done.
         *
         * @param decisions the conditions taken in on the way here, in the order they were assumed
         */
        T conditionsThatCannotAllHold(List<PathDecision> decisions);

        /**
         * Every case the arm is written for is one the rules refuse at the position matched on.
         *
         * <p>Unconditional, so it holds as truly under three enclosing arms as at the first fork: a
         * refusal is about the position and not about the way here.
         *
         * @param position how the position is spelled where a rule about it is written
         * @param cases    the cases the arm names, every one of them refused there
         */
        T everyCaseRefused(String position, List<TypeSymbol> cases);
    }

    /** What this proof comes to, in {@code words}. */
    <T> T said(Words<T> words);

    /** @see Words#conditionsThatCannotAllHold */
    static Proof conditionsThatCannotAllHold(List<PathDecision> decisions) {
        return new ConditionsThatCannotAllHold(decisions);
    }

    /** @see Words#everyCaseRefused */
    static Proof everyCaseRefused(String position, List<TypeSymbol> cases) {
        return new EveryCaseRefused(position, cases);
    }
}

record ConditionsThatCannotAllHold(List<PathDecision> decisions) implements Proof {

    ConditionsThatCannotAllHold {
        decisions = List.copyOf(decisions);
        if (decisions.isEmpty()) {
            throw new IllegalArgumentException(
                    "conditions that cannot all hold, with no condition among them");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.conditionsThatCannotAllHold(decisions);
    }
}

record EveryCaseRefused(String position, List<TypeSymbol> cases) implements Proof {

    EveryCaseRefused {
        cases = List.copyOf(cases);
        if (cases.isEmpty()) {
            throw new IllegalArgumentException("every case refused, of no cases");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.everyCaseRefused(position, cases);
    }
}
