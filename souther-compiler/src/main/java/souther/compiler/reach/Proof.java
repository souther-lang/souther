package souther.compiler.reach;

import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.NumericDomain;
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
public sealed interface Proof
        permits ConditionsThatCannotAllHold, OutsideInputDomain, EveryCaseRefused,
        NoCaseTheValueCanBeIsTaken, TheDeclarationHoldsNoneOf, TheDeclarationHoldsNothingElse {

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
         * The values the branch is written for are not values the position can hold.
         *
         * <p>Nearer than the general form and about a different thing. What contradicts the branch
         * here is what the declarations guarantee of the input, not what the guards above it
         * established — the condition alone leaves nothing, wherever in the body it stands. An
         * author reading the general form would be sent to look at the guards above, and there is
         * nothing there to find.
         *
         * @param position  where the value the branch turns on sits
         * @param admits    what the rules leave that position
         * @param departure the condition, and the way this branch takes it
         */
        T outsideInputDomain(TermPath position, NumericDomain.Bounds admits,
                             PathDecision departure);

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

        /**
         * What the arm matches on is a value the source wrote, and none of the cases it can be is
         * one the arm takes.
         *
         * <p>About what the {@code match} is handed and not about any position: a helper handed a
         * case at its call takes the arm for that case and no other, whatever the rules of the input
         * leave.
         *
         * @param canBe the cases the value matched on can be
         * @param cases the cases the arm names
         */
        T noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe, List<TypeSymbol> cases);

        /**
         * The position matched on is declared as a sum none of whose cases is one the arm is for.
         *
         * <p>About the type the input declares at the position and not about any rule: what a
         * shared helper matches on can be wider than what the behavior calling it takes, and the
         * cases the behavior's input leaves out are ones no value of it is.
         *
         * @param position how the position is spelled
         * @param declared every case the position's type holds
         * @param cases    the cases the arm needs a value to be, none of them among {@code declared}
         */
        T theDeclarationHoldsNoneOf(String position, List<TypeSymbol> declared,
                                    List<TypeSymbol> cases);

        /**
         * The position matched on is declared as a sum every case of which this arm needs a value
         * not to be.
         *
         * <p>The other side of the same fact: the arms before this one take every case the input
         * declares at the position, so what is left for this one is a case no value of it is.
         *
         * @param position how the position is spelled
         * @param declared every case the position's type holds
         * @param cases    the cases the arm needs a value not to be, {@code declared} among them
         */
        T theDeclarationHoldsNothingElse(String position, List<TypeSymbol> declared,
                                         List<TypeSymbol> cases);
    }

    /** What this proof comes to, in {@code words}. */
    <T> T said(Words<T> words);

    /** The conditions on the way here cannot all hold; see
     *  {@link Words#conditionsThatCannotAllHold}. */
    static Proof conditionsThatCannotAllHold(List<PathDecision> decisions) {
        return new ConditionsThatCannotAllHold(decisions);
    }

    /** The position would have to hold a value its input domain does not admit; see
     *  {@link Words#outsideInputDomain}. */
    static Proof outsideInputDomain(TermPath position, NumericDomain.Bounds admits,
                                    PathDecision departure) {
        return new OutsideInputDomain(position, admits, departure);
    }

    /** Every case the position could hold was refused; see {@link Words#everyCaseRefused}. */
    static Proof everyCaseRefused(String position, List<TypeSymbol> cases) {
        return new EveryCaseRefused(position, cases);
    }

    /** The value matched on is never a case the arm takes; see
     *  {@link Words#noCaseTheValueCanBeIsTaken}. */
    static Proof noCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe, List<TypeSymbol> cases) {
        return new NoCaseTheValueCanBeIsTaken(canBe, cases);
    }

    /**
     * The position's declared cases are none of the ones the arm needs a value to be, where
     * {@code among}, or all among the ones it needs a value not to be, where not; see
     * {@link Words#theDeclarationHoldsNoneOf} and {@link Words#theDeclarationHoldsNothingElse}.
     */
    static Proof theDeclarationLeavesNoCase(String position, List<TypeSymbol> declared,
                                            List<TypeSymbol> cases, boolean among) {
        return among ? new TheDeclarationHoldsNoneOf(position, declared, cases)
                : new TheDeclarationHoldsNothingElse(position, declared, cases);
    }
}

record TheDeclarationHoldsNoneOf(String position, List<TypeSymbol> declared,
                                 List<TypeSymbol> cases) implements Proof {

    TheDeclarationHoldsNoneOf {
        declared = List.copyOf(declared);
        cases = List.copyOf(cases);
        if (declared.isEmpty() || cases.isEmpty()) {
            throw new IllegalArgumentException(
                    "a declaration holding none of an arm's cases, with no case either way");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.theDeclarationHoldsNoneOf(position, declared, cases);
    }
}

record TheDeclarationHoldsNothingElse(String position, List<TypeSymbol> declared,
                                      List<TypeSymbol> cases) implements Proof {

    TheDeclarationHoldsNothingElse {
        declared = List.copyOf(declared);
        cases = List.copyOf(cases);
        if (declared.isEmpty() || cases.isEmpty()) {
            throw new IllegalArgumentException(
                    "a declaration holding nothing but what an arm is past, with no case either"
                            + " way");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.theDeclarationHoldsNothingElse(position, declared, cases);
    }
}

record NoCaseTheValueCanBeIsTaken(List<TypeSymbol> canBe, List<TypeSymbol> cases)
        implements Proof {

    NoCaseTheValueCanBeIsTaken {
        canBe = List.copyOf(canBe);
        cases = List.copyOf(cases);
        if (canBe.isEmpty() || cases.isEmpty()) {
            throw new IllegalArgumentException(
                    "a value never a case an arm takes, with no case either way");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.noCaseTheValueCanBeIsTaken(canBe, cases);
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

record OutsideInputDomain(TermPath position, NumericDomain.Bounds admits, PathDecision departure)
        implements Proof {

    OutsideInputDomain {
        if (position == null || admits == null || departure == null) {
            throw new IllegalArgumentException(
                    "a position outside what it holds, with no position, no bounds or no branch");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.outsideInputDomain(position, admits, departure);
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
