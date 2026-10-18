package souther.compiler.meaning;

import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Extreme;
import souther.compiler.core.Core;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Predicate;

/**
 * A number a comparison is written over, told apart by which value it is.
 *
 * <p>Wider than what a row controls ({@link DecisionAtom}). A value the body bound to a name — what
 * a dependency answered under {@code let x = opaque()}, what an attempt built — is no position a
 * row writes at, and it is still one value however often it is compared: {@code x < 5} and
 * {@code x < 6} are about one number, and the second follows from the first whatever the number
 * is. Not knowing what a value is computed from is not the same as not knowing which value it is,
 * and only the second leaves a comparison over it with nothing to say.
 */
public sealed interface Quantity permits DecisionAtom, Quantity.OfABinding,
        Quantity.HowManyMeet, Quantity.HowManyHold, Quantity.HowManyDifferent, Quantity.SumOver,
        Quantity.CodePointsOfAPiece, Quantity.RemainderOfADividend, Quantity.ProductOfTwo,
        Quantity.WhatAnOperationAnswers, Quantity.HowManyCarried {

    /**
     * How many what a recursion carries holds, whatever that is: what a walk carried into the step
     * being read, or what a call of a search answers one node down.
     *
     * <p>Made only while the step or the body is read for how many it answers, which a reading does
     * to show it is that many and a number of the element or the node, for every number there is:
     * a form over a number standing for any says so of each by its weight. What the reading
     * concludes has none of these in it, so no reader of what a condition states is handed one.
     */
    record HowManyCarried(ACarriedValue value) implements Quantity {

        public HowManyCarried {
            Objects.requireNonNull(value, "what is carried is some walk's");
        }

        /** Whether {@code form} reads this anywhere, in a number it is over or in one inside it. */
        public boolean isIn(LinearForm<Quantity> form) {
            return form.coefs().keySet().stream().anyMatch(this::isIn);
        }

        /** Whether {@code number} is this, or is made of a number or a statement that reads it. */
        public boolean isIn(Quantity number) {
            return switch (number) {
                case HowManyCarried other -> equals(other);
                case DecisionAtom.OfTheInput _, DecisionAtom.TakenOfAnAnswer _,
                     DecisionAtom.OfAnAnswer _, OfABinding _, CodePointsOfAPiece _,
                     RemainderOfADividend _, ProductOfTwo _, HowManyDifferent _ -> false;
                case WhatAnOperationAnswers answers -> answers.of().stream().anyMatch(this::isIn);
                case SumOver sum -> isIn(sum.ofTheElement());
                case HowManyHold held -> held.each().stream().anyMatch(this::isIn);
                case HowManyMeet count -> isIn(count.ofTheElement());
            };
        }

        /** Whether {@code stated} compares a number that reads this, or holds a statement that
         *  does. */
        public boolean isIn(Proposition stated) {
            return switch (stated) {
                case Proposition.Compared compared -> switch (compared.relation()) {
                    case Relation.Affine affine -> isIn(affine.form());
                    case Relation.Ordered ordered -> isIn(ordered.term());
                };
                case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                     Proposition.Present _, Proposition.SameValue _, Proposition.LastToHold _,
                     Proposition.Carried _, Proposition.Unread _ -> false;
                case Proposition.All _, Proposition.Any _, Proposition.OnAnApplication _,
                     Proposition.SoManyHold _, Proposition.Some _, Proposition.SomeReachable _,
                     Proposition.WhereItAnswers _ ->
                        stated.partsHeld().stream().anyMatch(this::isIn);
            };
        }

        /** What a reader handed one of these is told: it is no number of anything it reads. */
        public IllegalStateException reachedAReader() {
            return new IllegalStateException(spelled() + " stands for any number inside a"
                    + " recursion's step, and reaches no reader of a condition");
        }

        @Override
        public String spelled() {
            return "#" + value;
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What an operation the library declares answers of values of the input, where nothing here
     * says what that answer is in terms of them: {@code String.lowercase(s)}, {@code
     * String.trim(String.lowercase(s))}.
     *
     * <p>One value, told apart by the operation and what it was handed, and by nothing else. Two of
     * them of one position are one value only where they are one operation of the same arguments:
     * {@code String.lowercase(s)} and {@code String.uppercase(s)} are both made of {@code s} and
     * are different values, so where they are made from is no part of which value this is. The
     * positions are asked for apart ({@link #positionsItIsMadeOf}), by a reader filing a relation
     * at them.
     *
     * <p>Every argument is a number of the input or another of these, so the value is one the input
     * settles. That rests on the language and not on this compiler: an operation the language
     * defines answers one value wherever it is written with the same arguments (spec
     * §invariant-discharge-terms), which is what lets two of these that are equal cancel. What a
     * behavior answered, or a function a body was handed, is no such value — an injected behavior
     * may answer differently each time it is asked — and is no operation of one. Something past
     * the input — what a dependency answered, a value the body bound — is no argument of one, and
     * a call handed it is not read as one.
     *
     * @param operation the operation applied
     * @param of        what it was handed, in the order it was handed them
     */
    record WhatAnOperationAnswers(ValueName.Stdlib operation, List<Quantity> of)
            implements Quantity {

        public WhatAnOperationAnswers {
            if (operation == null || of == null || of.isEmpty()) {
                throw new IllegalArgumentException("an answer is some operation's, of something");
            }
            of = List.copyOf(of);
            for (Quantity each : of) {
                if (!(each instanceof DecisionAtom.OfTheInput)
                        && !(each instanceof WhatAnOperationAnswers)) {
                    throw new IllegalArgumentException("an operation's answer read here is of"
                            + " values of the input: " + each);
                }
            }
        }

        /** The numbers of the input this answer is made of, each once, in the order they are
         *  handed in. */
        public List<NumericTerm> positionsItIsMadeOf() {
            List<NumericTerm> out = new ArrayList<>();
            for (Quantity each : of) {
                List<NumericTerm> these = switch (each) {
                    case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
                    case WhatAnOperationAnswers inner -> inner.positionsItIsMadeOf();
                    default -> throw new IllegalStateException("held out by the constructor");
                };
                these.stream().filter(term -> !out.contains(term)).forEach(out::add);
            }
            return List.copyOf(out);
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder(operation.qualified()).append('(');
            for (int i = 0; i < of.size(); i++) {
                out.append(i == 0 ? "" : ", ").append(of.get(i).spelled());
            }
            return out.append(')').toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What a division by a written number leaves of a form of the input's numbers: the remainder of
     * {@code a - d} by seven, of the length of a list by eleven.
     *
     * <p>A number of its own and no position's. It runs from nought to one below the divisor
     * whatever the form comes to, and which rows stand at one of its values is which values of the
     * form leave it — a class of values of the form and no line on it, so a rule about it is a line
     * on the remainder and never on the form.
     *
     * <p>Whole numbers throughout. A form that weighs a number by a fraction, or is moved by one, is
     * no dividend of a remainder, and nothing here reads it as one.
     *
     * @param operation the library's floor remainder that answers it
     * @param dividend the form the division is of, constant included
     * @param divisor the number it is divided by, above nought
     */
    record RemainderOfADividend(ValueName operation, LinearForm<NumericTerm> dividend,
                                BigInteger divisor) implements Quantity {

        public RemainderOfADividend {
            if (operation == null || dividend == null || dividend.coefs().isEmpty()
                    || divisor == null || divisor.signum() <= 0
                    || DefaultBoundOperationFacts.get().divisorOfAFloorRemainder(operation)
                            .isEmpty()) {
                throw new IllegalArgumentException("a remainder is a floor remainder of a form of"
                        + " some numbers by a divisor above nought: " + operation + " of "
                        + dividend + " by " + divisor);
            }
        }

        /** What the operation was handed beside the dividend: the divisor, where it takes it. */
        public TakenArguments arguments() {
            return TakenArguments.at(
                    DefaultBoundOperationFacts.get().divisorOfAFloorRemainder(operation)
                            .getAsInt(), new BigDecimal(divisor));
        }

        /**
         * Where the operation states its answers lie by this divisor, whatever the dividend comes
         * to — the same account a remainder of one place is bounded by
         * ({@link NumericTerm.TakenOf#whatTheOperationStates}).
         */
        public NumericDomain.Bounds whatTheOperationStates() {
            TakenArguments given = arguments();
            return ResultRange.of(DefaultBoundOperationFacts.get().boundsOnTheResult(operation),
                    argument -> Optional.ofNullable(given.at(argument.position())));
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder("floorMod(");
            NumericTerms.entriesInOrder(dividend.coefs()).forEach(each -> out
                    .append(out.charAt(out.length() - 1) == '(' ? "" : " + ")
                    .append(each.getValue().spelled()).append('·').append(each.getKey()));
            if (dividend.constant().signum() != 0) {
                out.append(" + ").append(dividend.constant().spelled());
            }
            return out.append(", ").append(divisor).append(')').toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What two whole numbers of the input come to multiplied, where neither is a constant and each
     * is the number of one position: a price times a quantity.
     *
     * <p>Whole numbers, which the reading that makes one sees to: a product of two is worked out at
     * a row and drawn a line on as a product of two whole numbers, and of decimals it is not made.
     *
     * <p>A number of its own and no form over the two. Fixing either factor leaves a form over the
     * other, weighed by the value fixed, so a rule about the product relates the two positions and
     * divides neither of them by a line of its own: where one stands, the other can be anywhere
     * the value fixed lets it be. Which values of a factor still leave the rule both ways is asked
     * of what the other reaches ({@link souther.compiler.inputs.WhatARelationLeavesUndivided}).
     *
     * <p>The factors in one order whichever was written first, so {@code q * p} is {@code p * q}.
     * Two of one position are a square, which no factor fixed turns into a form of the other, and
     * are not one of these.
     *
     * @param one   the factor first in the order of terms
     * @param other the other factor
     */
    record ProductOfTwo(NumericTerm.FromOnePosition one, NumericTerm.FromOnePosition other)
            implements Quantity {

        public ProductOfTwo {
            if (one == null || other == null) {
                throw new IllegalArgumentException("a product is of two numbers");
            }
            if (one.position().equals(other.position())) {
                throw new IllegalArgumentException("a product of two numbers of one position is no"
                        + " relation between two: " + one + " and " + other);
            }
            List<NumericTerm> ordered = NumericTerms.inOrder(List.of(one, other));
            NumericTerm.FromOnePosition first = (NumericTerm.FromOnePosition) ordered.get(0);
            other = first == one ? other : one;
            one = first;
        }

        /** Both factors, in their order. */
        public List<NumericTerm.FromOnePosition> factors() {
            return List.of(one, other);
        }

        @Override
        public String spelled() {
            return one + " * " + other;
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many of the code points of one piece of a string are in a class.
     *
     * <p>Of a piece and of no input position: what a split by one code point leaves of a string,
     * and each character it is taken apart into, stands at no place a row writes, and the piece is
     * whichever one the statement it is read inside is about. So it is no number of the input and
     * only appears inside a statement about some piece, which holds against one of them is what
     * the string holds ({@link Derivation.SomePieceMeeting}) — and is never compared on its own.
     * Of a character, one code point, it is nought or one.
     *
     * <p>Which statement that is, is {@code within}: how many statements about some piece of a
     * string it is read inside of, the outermost being nought. A statement about some piece read
     * inside another one names two pieces, and a count of the outer piece is no count of the inner.
     */
    record CodePointsOfAPiece(CodePointClass counted, int within) implements Quantity {

        public CodePointsOfAPiece {
            if (counted == null) {
                throw new IllegalArgumentException("code points of a piece are counted by a class");
            }
            if (within < 0) {
                throw new IllegalArgumentException(
                        "a piece is of a statement some number of statements in: " + within);
            }
        }

        @Override
        public String spelled() {
            return "#(" + counted + ")(a piece " + within + " in)";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many different values stand at {@code ofTheElement} over the elements of the container
     * at {@code container}: the element itself, a position inside it, or the key it is filed under
     * — two of them one value where they are equal. Never more than the container holds, and
     * nought exactly where it holds nothing.
     *
     * <p>A number about every pair of elements and not about each: whether one adds to it turns on
     * the ones beside it, so it is no count of elements meeting something.
     */
    record HowManyDifferent(DecisionSubject container, DecisionSubject ofTheElement)
            implements Quantity {

        public HowManyDifferent {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("the values are of a container's elements");
            }
            if (!oneOfEach(container, ofTheElement)) {
                throw new IllegalArgumentException(ofTheElement + " is no one value of each"
                        + " element of " + container);
            }
        }

        /**
         * Whether {@code ofTheElement} is one value of each element of the container at
         * {@code container}: the element, a place inside it, or the key it is filed under, and no
         * place inside another container inside it. A place in a container inside the element is
         * as many values as that container holds, and how many differ among those is no number of
         * the elements — it may be more of them than there are elements.
         */
        public static boolean oneOfEach(DecisionSubject container, DecisionSubject ofTheElement) {
            return (ofTheElement.isAtOrUnder(container.element())
                    || ofTheElement.isAtOrUnder(container.key()))
                    && ofTheElement.howManyContainersHoldIt()
                            == container.howManyContainersHoldIt() + 1;
        }

        @Override
        public String spelled() {
            return "#different " + container + " [" + ofTheElement + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What {@code ofTheElement}, a number of each element of the container at {@code container},
     * adds up to over all of them: how many the lists inside a list hold between them, say. The
     * input's own totals are of a value standing at one position inside each element
     * ({@code NumericTerm.TakenOver}); this is of any number of the element.
     *
     * <p>Of one number of the element. A sum is linear, so a sum of a form is the form's weights
     * over the sums of its numbers and its constant times how many elements there are
     * ({@link #over}); held whole, one sum written two ways would be two quantities.
     */
    record SumOver(DecisionSubject container, Quantity ofTheElement) implements Quantity {

        public SumOver {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a sum is of a number of each element");
            }
        }

        /**
         * What {@code each}, a form over numbers of each element of the container at
         * {@code container}, adds up to over all of them: each number's weight on the sum of that
         * number, and the constant on {@code size}, how many elements there are — or null where
         * the constant is not nought and no size is in hand.
         */
        public static LinearForm<Quantity> over(DecisionSubject container,
                                                LinearForm<Quantity> each, Quantity size) {
            Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
            each.coefs().forEach((number, by) -> coefs.put(new SumOver(container, number), by));
            if (each.constant().signum() != 0) {
                if (size == null) {
                    return null;
                }
                coefs.put(size, each.constant());
            }
            return new LinearForm<>(ExactRatio.ZERO, coefs);
        }

        /**
         * What each element adds, where {@code sum} is a sum over the elements of the container at
         * {@code container} as {@link #over} spreads one: each sum's weight on the number it sums,
         * and the weight of how many elements there are, which {@code howMany} tells, as the
         * constant — or null where some part of {@code sum} is neither.
         */
        public static LinearForm<Quantity> addedByEach(DecisionSubject container,
                                                       LinearForm<Quantity> sum,
                                                       Predicate<Quantity> howMany) {
            if (sum.constant().signum() != 0) {
                return null;
            }
            Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
            ExactRatio constant = ExactRatio.ZERO;
            for (Map.Entry<Quantity, ExactRatio> part : sum.coefs().entrySet()) {
                if (part.getKey() instanceof SumOver(DecisionSubject summed, Quantity each)
                        && summed.equals(container)) {
                    coefs.put(each, part.getValue());
                } else if (howMany.test(part.getKey()) && constant.signum() == 0) {
                    constant = part.getValue();
                } else {
                    return null;
                }
            }
            return new LinearForm<>(constant, coefs);
        }

        @Override
        public String spelled() {
            return "#sum " + container + " [" + ofTheElement.spelled() + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many of these statements hold: what a closure states of each value a container was
     * written with, one statement for each.
     *
     * <p>No count of a container the input holds. The values are written out, so each is a
     * statement of its own about the input, and how many of them hold against a number is which of
     * them hold — said that way where it is compared ({@link Proposition#compared}). Of statements
     * none of which is settled: one that is settled is already a number, and is added beside this.
     *
     * <p>Whether a comparison of it is written out as its choices or held as the count turns on how
     * many choices and parts those come to ({@link Proposition.SoManyHold}), and is no part of what
     * is counted.
     */
    record HowManyHold(List<Proposition> each) implements Quantity {

        public HowManyHold {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("how many of no statements hold is none");
            }
            if (each.stream().anyMatch(one -> one instanceof Proposition.Always)) {
                throw new IllegalArgumentException("a settled statement is a number, and not one"
                        + " of these: " + each);
            }
            if (each.stream().anyMatch(Proposition::mayAnswerNothing)) {
                throw new IllegalArgumentException("a count is of statements answering on every"
                        + " row: " + each);
            }
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder("#[");
            for (int i = 0; i < each.size(); i++) {
                out.append(i == 0 ? "" : ", ").append(each.get(i).key());
            }
            return out.append("]").toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many elements of the container at {@code container} meet {@code ofTheElement}: never
     * fewer than none, never more than the container holds, and none exactly where no element
     * meets it.
     *
     * <p>A number with a statement inside, and not a value of the input: what it is turns on every
     * element, so held against nought it is that statement quantified ({@link
     * Proposition#compared}), and held against any other number it says how many, which is kept
     * as the relation. What it is about is the element where it stands, so two counts written with
     * their elements named differently are one count.
     *
     * <p>Only of a statement that may come out one way for one element and the other way for
     * another, and only of a statement read through: a count of what is the same for every element
     * is the container's size or none, and a count of what nobody read is no number anything can be
     * said of.
     */
    record HowManyMeet(DecisionSubject container, Proposition ofTheElement) implements Quantity {

        public HowManyMeet {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a count is of the elements of some container");
            }
            if (!ofTheElement.mayTurnOnAnElementOf(container)) {
                throw new IllegalArgumentException("a count of " + ofTheElement
                        + " is the same for every element of " + container);
            }
            if (Proposition.mayAnswerNothing(ofTheElement)) {
                throw new IllegalArgumentException("a count is of a statement answering on every"
                        + " element: " + ofTheElement);
            }
            if (Proposition.leavesSomethingUnread(ofTheElement)) {
                throw new IllegalArgumentException("a count is of a statement read through, and "
                        + ofTheElement + " was not");
            }
        }

        /**
         * That some element meets what is counted: the count being one or more, which is what it
         * is wherever a count is held against nought ({@link Proposition#compared}).
         */
        public Proposition someMeets() {
            return new Proposition.Some(container, ofTheElement, true);
        }

        @Override
        public String spelled() {
            return "#" + container + " [" + ofTheElement.key() + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What this quantity is, as an identity spells it.
     *
     * <p>Whole, so that two quantities are one exactly where they are the same thing. A dependency
     * is written under the module that declares it: two modules may declare behaviors of one name,
     * and a spelling that left the module off would make the order two quantities come in — and so
     * which way a comparison over them faces ({@link Relation.OneWay}) — turn on which of them a
     * reader happens to meet.
     */
    String spelled();

    /**
     * What a walk whose step keeps one end of what it carried and a value of the element
     * ({@code SeededWalk.endKept}) carries into the step on an element: that end of its seed and
     * of the value on every element before it.
     *
     * <p>So it lies between the seed and the furthest value an element may hold past it, and is
     * the seed on the first element. It is no value of the element the step is applied to, which
     * is why it is apart from that element's numbers where nothing ties the elements of the
     * container to one another, nor the seed to them.
     *
     * @param extreme   which end the step keeps
     * @param seed      what the walk starts from
     * @param container the container the walk walks
     * @param ofEach    the number of the element the step keeps an end of
     * @param howMany   how many the container holds, or null where that is no number read
     */
    record KeptSoFar(Extreme extreme, Seed seed, TermPath container,
                     NumericTerm.FromOnePosition ofEach, NumericTerm.FromOnePosition howMany) {

        public KeptSoFar {
            Objects.requireNonNull(extreme, "a walk keeps one end");
            Objects.requireNonNull(seed, "a walk starts from something");
            Objects.requireNonNull(container, "a walk walks some container");
            Objects.requireNonNull(ofEach, "and keeps an end of some number of the element");
            if (!ofEach.placesReadOff().stream()
                    .allMatch(place -> place.isAtOrUnder(container.element()))) {
                throw new IllegalArgumentException("what is kept is read off the elements: "
                        + ofEach + " of " + container);
            }
            if (seed instanceof Seed.OfTheInput(var at) && at.placesReadOff().stream()
                    .anyMatch(place -> place.isAtOrUnder(container))) {
                throw new IllegalArgumentException("a seed is one value of the run, and no"
                        + " element of what is walked: " + at + " of " + container);
            }
            if (seed instanceof Seed.OfTheKey(var key, var _)
                    && !key.isAtOrUnder(container.element())) {
                throw new IllegalArgumentException("a key is read off the elements: " + key
                        + " of " + container);
            }
        }

        /** What a walk keeping an end starts from: a number written out, one number of the
         *  input, which is one value on a run whatever the elements are, or nothing — the first
         *  element of a key files its own value. */
        public sealed interface Seed {

            /** A number written out. */
            record Written(ExactRatio number) implements Seed {}

            /** A number of the input outside what is walked. */
            record OfTheInput(NumericTerm.FromOnePosition number) implements Seed {}

            /**
             * Nothing: the walk files what each element holds under its key, so the end kept is of
             * the elements before it that have the same key, and an element with a key no earlier
             * element has is compared with nothing.
             *
             * @param key       where the key stands in an element
             * @param reachedBy the arm of a match on a lookup of the key that is entered only where
             *                  an earlier element has the key, where the walk looks the key up and
             *                  does not hand a closure the value found
             */
            record OfTheKey(TermPath key, Optional<Core.Case> reachedBy) implements Seed {

                public OfTheKey {
                    Objects.requireNonNull(key, "a key stands somewhere in an element");
                    Objects.requireNonNull(reachedBy, "an arm, or none");
                }
            }
        }
    }

    /**
     * The number at {@code steps} below the value bound at {@code binding}: one value, by the
     * binding that names it and nothing else.
     *
     * <p>By the binding and not by what it was bound to. Two calls of one dependency with one
     * argument are two answers, and a value named twice is one; what tells them apart is which
     * name stands for which, which is what the binding is.
     *
     * <p>A field read that reaches nowhere else — the value inside a newtype — is no step, so
     * {@code x.value} and {@code x} are one quantity, as they are one place.
     *
     * <p>What the value was made from is no part of a statement about it, and is carried beside
     * the binding only as far as a reader is owed: where the reading of it stopped, which is why
     * the number is none of the input's. A reader that takes a fact about the value takes all the
     * statement says, and one that cannot settle something past it says that this was what it
     * could not read. Empty where nothing of the value was read to stop — an answer a dependency
     * gave, what an attempt built — since there is nothing it is made of to read.
     *
     * <p>Where the value is what a walk keeping an end carried into its step, which end it is of
     * what is carried beside it ({@link KeptSoFar}). That says where the value may lie and which of
     * those values it is shown to take, and still nothing of which value it is on a run.
     *
     * @param binding which binding names the value
     * @param steps   the steps read off it that go somewhere, outermost first
     * @param type    what stands there, which is how its numbers are spaced
     * @param madeOf  why what the value was made from is no number of the input, where the
     *                reading met it and stopped
     * @param kept    the end a walk has kept by the element its step is applied to, where the
     *                value is what the walk carried into the step
     */
    record OfABinding(BindingId binding, List<TermPath.Step> steps, Type type,
                      Optional<WhyUnread> madeOf, Optional<KeptSoFar> kept)
            implements Quantity {

        public OfABinding {
            if (binding == null || type == null || madeOf == null || kept == null) {
                throw new IllegalArgumentException("a bound number is some binding's, of some type");
            }
            steps = List.copyOf(steps);
            if (kept.isPresent() && (madeOf.isPresent() || !steps.isEmpty())) {
                throw new IllegalArgumentException("what a walk carried is the value itself, and"
                        + " nothing of it was read to stop: " + binding);
            }
        }

        @Override
        public String spelled() {
            StringBuilder out = new StringBuilder(binding.toString());
            steps.forEach(each -> out.append('.').append(each));
            return out.toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }
}
