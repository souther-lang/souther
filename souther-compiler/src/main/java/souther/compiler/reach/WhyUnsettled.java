package souther.compiler.reach;

import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.Unsettlement;

/**
 * Why a reading could not say whether anything arrives.
 *
 * <p>Not the same question as why a position's declarations left a distinction open
 * ({@link Unsettlement}), which is about what the rules of a type came to. This is about a place in
 * a body and the conditions on the way to it.
 *
 * <p>The reasons are kept apart because they are owed different things. A condition of a shape this
 * reading has no rule for is this compiler's limit, and widening the reading removes it. Nothing to
 * show that something arrives is not a limit at all — it is the ordinary state of a place nobody
 * built a value for and no run reached, and it stays that way however wide the reading gets.
 *
 * <p>Taken apart by writing the sentences and no other way, as {@link Proof} is, and for the same
 * reason: the readers that decide read the three answers, and the one reader that writes words
 * about this says a word for every arm or does not compile.
 */
public sealed interface WhyUnsettled
        permits NoWitness, AConditionWasNotRead, ThePositionDidNotSettleIt, TheWalkDidNotReachIt {

    /** The sentences a reason can come to, one per arm. */
    interface Words<T> {

        /**
         * Nothing contradicted, and nothing shows anything arrives either.
         *
         * <p>The usual answer, and the one that keeps a claim from being refuted on a domain's
         * silence.
         */
        T noWitness();

        /**
         * A condition on the way here is of a shape this reading has no rule for, so what it
         * settles was not taken in.
         *
         * <p>Left out rather than guessed at, which is what keeps the proofs sound: a reading that
         * took nothing in ruled nothing out. What it costs is this answer.
         *
         * @param at where the condition is written
         */
        T aConditionWasNotRead(SourcePos at);

        /**
         * The rules of the position an arm matches on did not settle whether its cases can stand
         * there.
         *
         * <p>Carried through rather than restated. Whether a distinction can stand at a position is
         * the position's own question and it has its own words for not settling it; a reading that
         * answered "no witness" here would drop what the position already said about why.
         */
        T thePositionDidNotSettleIt(Unsettlement why);

        /** The walk did not get to it: something it could not read stood in the way, or it stopped
         *  at the depth it opens branches to. */
        T theWalkDidNotReachIt();
    }

    /** What this reason comes to, in {@code words}. */
    <T> T said(Words<T> words);

    /** Nothing was found that would show it; see {@link Words#noWitness}. */
    static WhyUnsettled noWitness() {
        return new NoWitness();
    }

    /** A condition on the way was of a shape no rule here reads; see
     *  {@link Words#aConditionWasNotRead}. */
    static WhyUnsettled aConditionWasNotRead(SourcePos at) {
        return new AConditionWasNotRead(at);
    }

    /** What is known of the position leaves it open; see
     *  {@link Words#thePositionDidNotSettleIt}. */
    static WhyUnsettled thePositionDidNotSettleIt(Unsettlement why) {
        return new ThePositionDidNotSettleIt(why);
    }

    /** The walk stopped before it got there; see {@link Words#theWalkDidNotReachIt}. */
    static WhyUnsettled theWalkDidNotReachIt() {
        return new TheWalkDidNotReachIt();
    }
}

record NoWitness() implements WhyUnsettled {

    @Override
    public <T> T said(Words<T> words) {
        return words.noWitness();
    }
}

record AConditionWasNotRead(SourcePos at) implements WhyUnsettled {

    AConditionWasNotRead {
        if (at == null) {
            throw new IllegalArgumentException("a condition written nowhere was not one");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.aConditionWasNotRead(at);
    }
}

record ThePositionDidNotSettleIt(Unsettlement why) implements WhyUnsettled {

    ThePositionDidNotSettleIt {
        if (why == null) {
            throw new IllegalArgumentException("a position unsettled by nothing settled it");
        }
    }

    @Override
    public <T> T said(Words<T> words) {
        return words.thePositionDidNotSettleIt(why);
    }
}

record TheWalkDidNotReachIt() implements WhyUnsettled {

    @Override
    public <T> T said(Words<T> words) {
        return words.theWalkDidNotReachIt();
    }
}
