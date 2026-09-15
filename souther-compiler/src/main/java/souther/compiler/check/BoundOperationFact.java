package souther.compiler.check;

import souther.compiler.core.DeclaredOperation;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.Accumulation;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.Arithmetic;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.DefinitionCase;
import souther.compiler.semantics.ElementShape;
import souther.compiler.semantics.NumericResult;
import souther.compiler.semantics.OperationSubject;
import souther.compiler.semantics.ResultBound;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.Set;

/**
 * A fact about an operation, once it has been held to the library that declares one.
 *
 * <p>What {@link souther.compiler.semantics.OperationFacts} states is written in the vocabulary
 * somebody authors a fact in: a {@link souther.compiler.types.ValueName} for the operation it is
 * about, an {@link souther.compiler.semantics.ArgumentRef} for an argument it names, another name
 * for an operation it relates this one to. None of those says the library has such an operation, or
 * that it takes an argument there, or that the two signatures let one stand for the other. That is
 * what {@link OperationFactBinder} settles against {@link souther.compiler.stdlib.Stdlib}, and
 * these are what the facts come to once it has: every operation is a {@link DeclaredOperation} and
 * every argument a {@link DeclaredArgument}, each read against its declaration.
 *
 * <p>A reader below the binding holds one of these and asks nothing further. Handed the authoring
 * value instead, it would have the name and the table and could put the same question again — and
 * would get an answer that agrees with the binder's for exactly as long as nobody changes either.
 *
 * <p><b>One arm per kind of authored fact, and every arm names its operation.</b> The binder's
 * switch over the authoring kinds is an expression yielding one of these, so a kind added there is
 * a kind that does not compile until it says what it comes to bound. The operation is on every arm
 * because that is what the fact is about, and it is the one thing a table of these is keyed by —
 * read off the fact itself, so no key is ever written beside a value that could disagree with it.
 *
 * <p><b>Two families, and every arm is in one of them.</b> {@link OneAboutAnOperation} is a kind of
 * which an operation carries at most one — a second declaration of it would be two answers to a
 * question that has one, and is refused where these are collected. {@link SeveralAboutAnOperation}
 * is a kind an operation states as many of as it states: two bounds are two facts. The family is
 * chosen where the arm is written, so a kind added cannot leave whether it may repeat to whichever
 * collector happens to receive it.
 *
 * <p><b>Made by the binder and by nothing else.</b> One of these says a fact was held to the
 * library, and that is true of a value only where the holding made it: an arm a reader wrote for
 * itself would say the same thing about a fact nothing checked. So this package's, and the
 * constructor of every arm is called by {@link OperationFactBinder} alone — counted from the class
 * files ({@code OnlyTheBinderReadsTheAuthoringVocabularyTest}) rather than trusted to a modifier,
 * since a name this package can reach is a name this package can call. The same is held of what
 * the arguments are made of ({@link DeclaredArgument}) and of what the arms are gathered into
 * ({@link BoundOperationFacts}), so the three steps from an authored fact to a fact a reader holds
 * are each taken in one place.
 */
sealed interface BoundOperationFact permits BoundOperationFact.OneAboutAnOperation,
        BoundOperationFact.SeveralAboutAnOperation {

    /** The operation this is about, read against its declaration. */
    DeclaredOperation operation();

    /** A kind of fact an operation carries at most one of. */
    sealed interface OneAboutAnOperation extends BoundOperationFact {}

    /** A kind of fact an operation may carry several of, each a statement of its own. */
    sealed interface SeveralAboutAnOperation extends BoundOperationFact {}

    /** What the operation answers, counted, is this form of what its arguments are counted as. */
    record AnswersAFormOfItsArguments(DeclaredOperation operation,
                                      LinearForm<DeclaredArgument> form)
            implements OneAboutAnOperation {}

    /** The sign of what the operation answers states which of these two arguments is the greater:
     *  {@code greater} where the answer is positive, and the other one where it is negative. */
    record StatesTheOrderOfItsArguments(DeclaredOperation operation, DeclaredArgument greater,
                                        DeclaredArgument lesser)
            implements OneAboutAnOperation {}

    /** The operation answers the value at {@code of} moved by {@code amount}, and how far it moved
     *  is {@code per} of what {@code measure} counts. */
    record ShiftsBy(DeclaredOperation operation, DeclaredOperation measure, DeclaredArgument of,
                    DeclaredArgument amount, BigDecimal per)
            implements OneAboutAnOperation {}

    /** The operation builds a container out of another, and this says where its elements came from
     *  and how many of them there are. */
    record BuildsItsResultFrom(DeclaredOperation operation, BuiltFrom<DeclaredArgument> built)
            implements OneAboutAnOperation {}

    /**
     * The operation answers what {@code container} holds accumulated: started from an identity and
     * carried through one step, both of the type the container's elements are — which the binding
     * held to be the type the operation answers.
     */
    record AccumulatesItsContainer(DeclaredOperation operation, DeclaredArgument container,
                                   Accumulation how)
            implements OneAboutAnOperation {

        /** The type the walk carries, which is what the container holds. */
        public Type element() {
            return Type.elementOfAContainer(container.stands());
        }

        /**
         * This walk put as a way of taking a number of the one value it is given, or null where it
         * is a walk this has no such reading of.
         *
         * <p>Only the walk that adds. A join carries an identity and a step as much as a sum does
         * and answers a string; a product carries them and answers a number no term-reading takes.
         * What is derived is one account and not the family, so the reading a term gets is one
         * something can carry out — and a walk of another kind arriving is a walk nothing here
         * claims to read.
         *
         * <p>Here and nowhere else. An accumulation over one container already says what the answer
         * is — start from this, carry that — so an account declared beside it would be the same
         * sentence in a second vocabulary, free to disagree about what a sum is. What reads it as a
         * term reads it off the walk, through this.
         */
        public TakenAs takenAs() {
            return how.identity() == Accumulation.Identity.ZERO
                    && how.combine() == Accumulation.Combine.ADD
                    ? new TakenAs.TheSumOfWhatItHolds() : null;
        }
    }

    /** The operation is a predicate over what {@code container} holds, and its statement survives a
     *  construction of the shapes in {@code through}. */
    record ReadsItsContainer(DeclaredOperation operation, DeclaredArgument container,
                             Set<ElementShape> through)
            implements OneAboutAnOperation {

        public ReadsItsContainer {
            through = Set.copyOf(through);
        }
    }

    /** What {@code argument} answers decides {@code aspect} of what the operation answers, which is
     *  the edge a rule written inside that argument reaches the call along. */
    record TurnsOnWhetherAnArgumentHolds(DeclaredOperation operation,
                                        AnswerAspect aspect,
                                        DeclaredArgument argument)
            implements OneAboutAnOperation {}

    /** The predicate is stated over a projection of each element, and {@code projection} is where
     *  it is written. */
    record IsStatedOverAProjection(DeclaredOperation operation, DeclaredArgument projection)
            implements OneAboutAnOperation {}

    /** The operation states its predicate of <em>every</em> element. */
    record StatesItsPredicateOfEveryElement(DeclaredOperation operation)
            implements OneAboutAnOperation {}

    /**
     * An emptiness check and the size it means, each read against its declaration.
     *
     * <p>What this carries that the authoring fact cannot: the two operations take the same
     * argument, and the second answers a number where the first answers a truth. A reader rewriting
     * one call into the other moves the arguments across unchanged, so those are the conditions
     * under which such a rewrite says the same thing — asked once, where both declarations are in
     * hand, rather than by the reader that has a call and a name.
     */
    record MeansTheSameAsASizeOfNought(DeclaredOperation operation, DeclaredOperation size)
            implements OneAboutAnOperation {}

    /** The operation computes a number, and this says which arithmetic and where it answers it. */
    record ComputesANumber(DeclaredOperation operation, NumericResult<DeclaredArgument> result)
            implements OneAboutAnOperation {

        /**
         * This arithmetic put as a way of taking a number of the value it computes over, for a call
         * whose other arguments read as {@code arguments} — or null where it is arithmetic this has
         * no such reading of, or where those arguments leave the number unsettled.
         *
         * <p><b>A reading of a call and not a second account of the operation.</b> What the
         * operation computes is the arithmetic, and that is the one representation of its number
         * ({@link NumericReadings}). This is that representation read for the calls it fits: a
         * quotient whose divisor the reading has as a constant is a number taken of what it divides,
         * exactly as an hour is a number taken of a time, and every other call of the same operation
         * is not. Declared beside the arithmetic instead, one operation would carry two accounts of
         * one number and the library would be refused where it was written.
         *
         * <p>Only the truncating quotient. What the operator arithmetic computes is a number of two
         * values and stays one when one of them is written down — {@code x + 2} is arithmetic the
         * affine walk composes rather than a number taken of {@code x} — so nothing is derived for
         * it: the walk that reads a form already reads those, and a term beside it would be a second
         * reader of one expression. A remainder is the quotient's companion and has an account of
         * its own to be written when something asks for it; a quotient rounded to a scale answers
         * on a grid the call chooses, which is not this arm.
         *
         * <p><b>And only where the call names a quotient there is.</b> Such an operation answers
         * its number at one case and something else at another, and which argument decides that is
         * what the declaration states — that argument is the divisor, and it is where the account
         * is written for. Whether the number this call takes is one the position has is the
         * account's own answer ({@link TakenAs#settledBy}), so what the operation may answer and
         * what this call takes stay two sentences.
         */
        public TakenAs takenAs(TakenArguments arguments) {
            if (!(result.computes() instanceof Arithmetic.ATruncatingQuotient)
                    || result.unless() == null) {
                return null;
            }
            // Which argument the divisor is, is the declaration's. Such an operation answers its
            // other case when one of its arguments stands a certain way, and for a quotient that
            // argument is the one it divides by — so the account is written for the position the
            // condition names rather than for a place written down here.
            TakenAs.TheTruncatingQuotient how =
                    new TakenAs.TheTruncatingQuotient(result.unless().argument().position());
            return how.settledBy(arguments) ? how : null;
        }
    }

    /** The operation answers a number taken of the one value it is given — {@code of}, the one
     *  argument its declaration takes — and {@code how} is what it takes of it; {@code answers} is
     *  the number it was held to answer. */
    record AnswersANumberTakenOfAValueItIsGiven(DeclaredOperation operation,
                                                     DeclaredArgument of, Type answers,
                                                     TakenAs how)
            implements OneAboutAnOperation {}

    /** Every number the operation could answer is one some value it could be given answers. */
    record EveryAnswerItCanGiveHasASourceValue(DeclaredOperation operation)
            implements OneAboutAnOperation {}

    /** Something that holds of the number the operation answers, wherever it is called. One per
     *  bound: an operation with two ends states two of these. */
    record BoundsItsResult(DeclaredOperation operation, ResultBound<DeclaredArgument> bound)
            implements SeveralAboutAnOperation {}

    /** The operation's result is never smaller than what {@code container} holds. One per
     *  container: {@code a ++ b} is as long as either half. */
    record ResultIsNoSmallerThan(DeclaredOperation operation, DeclaredArgument container)
            implements SeveralAboutAnOperation {}

    /** One case of the definition the operation is written in. The cases of one operation are
     *  exhaustive between them, in the order they are declared. */
    record IsDefinedByCases(DeclaredOperation operation, DefinitionCase<DeclaredArgument> one)
            implements SeveralAboutAnOperation {}

    /** There is nothing to say of the operation under {@code subject}. As many as there are
     *  subjects it is silent under, and one per subject — a second under one subject is refused
     *  where the silences are gathered ({@link BoundOperationFacts}). */
    record SaysNothingOf(DeclaredOperation operation, OperationSubject subject)
            implements SeveralAboutAnOperation {}
}
