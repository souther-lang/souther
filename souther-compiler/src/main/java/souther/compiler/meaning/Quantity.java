package souther.compiler.meaning;

import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Extreme;
import souther.compiler.core.EnteredArm;
import souther.compiler.inputs.ElementKey;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.ValueTransformation;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.ResultRange;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
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
        Quantity.HowManyMeet, Quantity.HowManyHold, Quantity.HowManyDifferent,
        Quantity.HowManyDifferentMeet, Quantity.HowManyDifferentBelow,
        Quantity.HowManyDifferentAcross, Quantity.SumOver, Quantity.TheKeptTotal,
        Quantity.CodePointsOfAPiece, Quantity.RemainderOfADividend,
        Quantity.RemainderByAnInput, Quantity.ProductOfTwo, Quantity.WhatAnOperationAnswers,
        Quantity.HowManyCarried, Quantity.APieceOf, Quantity.ThePieceAt,
        Quantity.IsAmongThePieces {

    /** Where the pieces a window holds begin, as a key spells it: nothing for the first. */
    private static String fromSpelled(int from) {
        return from > 0 ? " from piece " + from : "";
    }

    /**
     * What a recursion carries, whatever that is: how many what a walk carried into the step
     * being read holds, the number a walk over the elements of an answer carried into its step, or
     * how many what a call of a search answers one node down holds.
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
                     DecisionAtom.ComputedOverAnAnswer _,
                     DecisionAtom.OfAnAnswer _, OfABinding _, CodePointsOfAPiece _,
                     RemainderOfADividend _, RemainderByAnInput _, ProductOfTwo _,
                     HowManyDifferent _, HowManyDifferentBelow _, HowManyDifferentAcross _,
                     TheKeptTotal _ -> false;
                case WhatAnOperationAnswers answers -> answers.of().stream().anyMatch(this::isIn);
                case APieceOf piece -> isIn(piece.string());
                case ThePieceAt piece -> isIn(piece.string());
                case IsAmongThePieces among -> isIn(among.value()) || isIn(among.string());
                case SumOver sum -> isIn(sum.ofTheElement());
                case HowManyHold held -> held.each().stream().anyMatch(this::isIn);
                case HowManyMeet count -> isIn(count.ofTheElement());
                case HowManyDifferentMeet different -> isIn(different.meeting().statement());
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
                case Proposition.StringInside inside ->
                        isIn(inside.inner()) || isIn(inside.outer());
                case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                     Proposition.Present _, Proposition.InTheStrings _, Proposition.SameValue _,
                     Proposition.LastToHold _, Proposition.Carried _,
                     Proposition.Unread _ -> false;
                case Proposition.All _, Proposition.Any _, Proposition.OnAnApplication _,
                     Proposition.SoManyHold _, Proposition.Some _, Proposition.SomeReachable _,
                     Proposition.WhereItAnswers _, Proposition.OfTheWays _ ->
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
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            List<Spelling> pieces = new ArrayList<>(2 * of.size() + 1);
            pieces.add(Spelling.of(operation.qualified() + "("));
            for (int i = 0; i < of.size(); i++) {
                if (i > 0) {
                    pieces.add(Spelling.SEPARATOR);
                }
                pieces.add(of.get(i).spelling());
            }
            pieces.add(Spelling.of(")"));
            return Spelling.joined(pieces);
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * One piece of the string {@code string} that {@code operation} parts: the value a statement
     * about some piece of it compares with another value.
     *
     * <p>A piece stands at no position a row writes, and it is whichever one the statement it is
     * read inside is about ({@link CodePointsOfAPiece}): a variable that statement binds, and one
     * that leaves it only as what the statement comes to for the string. A comparison of a piece
     * with a value is a statement about that piece alone, and "some piece is the value" is not
     * "the piece is the value" held once — nor is its denial "the piece is another value" — so
     * what leaves the statement is {@link IsAmongThePieces}, which says it of all the pieces.
     * Told apart by the string, the separator and {@code within}, which is how many statements
     * about some piece it is read inside of: two pieces of one string read in two statements are
     * two values, and one read in a single statement is one.
     *
     * @param operation the library's operation that parts the string
     * @param separator the code point it is parted at, or none where it parts into characters
     * @param string    the string, a number of the input or what an operation answers of one
     * @param within    how many statements about some piece this one is read inside of
     * @param from      the index of the first piece it may be, nought where it may be the first
     * @param among     the index the pieces it may be stop before, or nought where they run to
     *                  the last: the piece of the first one and the piece of the first two are
     *                  two values, as a string can hold the value in its second piece alone,
     *                  and so are those of the pieces from the second on and from the third
     */
    record APieceOf(ValueName.Stdlib operation, OptionalInt separator, Quantity string,
                    int within, int from, int among) implements Quantity {

        public APieceOf {
            Objects.requireNonNull(operation, "a piece is of what some operation parts");
            Objects.requireNonNull(separator, "parted at a code point, or into characters");
            if (!(string instanceof DecisionAtom.OfTheInput)
                    && !(string instanceof WhatAnOperationAnswers)) {
                throw new IllegalArgumentException(
                        "a piece read here is of a string of the input: " + string);
            }
            if (within < 0) {
                throw new IllegalArgumentException(
                        "a piece is of a statement some number of statements in: " + within);
            }
            if (from < 0 || among < 0 || (among > 0 && among <= from)) {
                throw new IllegalArgumentException(
                        "a piece is one of the pieces from one index to a later one: " + from
                                + " " + among);
            }
        }

        /** The numbers of the input the string is made of, each once. */
        public List<NumericTerm> positionsItIsMadeOf() {
            return switch (string) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
                case WhatAnOperationAnswers answers -> answers.positionsItIsMadeOf();
                default -> throw new IllegalStateException("held out by the constructor");
            };
        }

        @Override
        public String spelled() {
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("a piece " + within + " in" + fromSpelled(from)
                    + (among > 0 ? " among the first " + among : "") + " of "
                    + operation.qualified() + "("
                    + (separator.isPresent() ? "U+" + Integer.toHexString(separator.getAsInt())
                            + ", " : ""), string.spelling(), ")");
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * The piece at an index of a string that an operation parts: one value, told apart by the
     * string, the separator and the index.
     *
     * <p>The piece a list lookup at an index written down picks of the pieces, which the arm that
     * opens the lookup binds. Beside {@link APieceOf}, which is whichever piece the statement it
     * is read inside is about: this is one piece, the one at the index, and it is there only where
     * the string has that many.
     *
     * @param operation the library's operation that parts the string
     * @param separator the code point it is parted at
     * @param string    the string, a number of the input or what an operation answers of one
     * @param index     which of the pieces it is, counting from nought
     */
    record ThePieceAt(ValueName.Stdlib operation, int separator, Quantity string, int index)
            implements Quantity {

        public ThePieceAt {
            Objects.requireNonNull(operation, "a piece is of what some operation parts");
            if (!(string instanceof DecisionAtom.OfTheInput)
                    && !(string instanceof WhatAnOperationAnswers)) {
                throw new IllegalArgumentException(
                        "a piece read here is of a string of the input: " + string);
            }
            if (index < 0) {
                throw new IllegalArgumentException("a piece is at an index of nought or more: "
                        + index);
            }
        }

        /** The numbers of the input the string is made of, each once. */
        public List<NumericTerm> positionsItIsMadeOf() {
            return switch (string) {
                case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
                case WhatAnOperationAnswers answers -> answers.positionsItIsMadeOf();
                default -> throw new IllegalStateException("held out by the constructor");
            };
        }

        @Override
        public String spelled() {
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("piece " + index + " of " + operation.qualified() + "(U+"
                    + Integer.toHexString(separator) + ", ", string.spelling(), ")");
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * Whether a value is one of the pieces of a string, as the number one where it is and nought
     * where it is not: the whole of what "some piece is the value" says, and the whole of what its
     * denial says, which is that no piece is.
     *
     * <p>A number, so it is held against one as any other is, and its denial is the other number.
     * The statement that some piece is not the value is not this one's denial and is not this at
     * all: it says which piece, and a string with two pieces has one that is the value and one that
     * is not. Compared with a value of the input it relates that value to the string, and divides
     * neither where the string has a piece for every value to be or not to be — which is why it is
     * made only of what always has one ({@code operation}'s answer is never empty).
     *
     * @param value     the value, a number of the input or what an operation answers of one
     * @param operation the library's operation that parts the string
     * @param separator the code point it is parted at, or none where it parts into characters
     * @param string    the string, a number of the input or what an operation answers of one
     * @param from      the index of the first piece it may be one of, nought for the first
     * @param among     the index the pieces it may be one of stop before, or nought where they
     *                  run to the last
     */
    record IsAmongThePieces(Quantity value, ValueName.Stdlib operation, OptionalInt separator,
                            Quantity string, int from, int among) implements Quantity {

        public IsAmongThePieces {
            Objects.requireNonNull(operation, "the pieces are what some operation parts");
            Objects.requireNonNull(separator, "parted at a code point, or into characters");
            for (Quantity each : List.of(value, string)) {
                if (!(each instanceof DecisionAtom.OfTheInput)
                        && !(each instanceof WhatAnOperationAnswers)) {
                    throw new IllegalArgumentException(
                            "a piece is compared here with a value of the input: " + each);
                }
            }
            if (from < 0 || among < 0 || (among > 0 && among <= from)) {
                throw new IllegalArgumentException(
                        "the value is one of the pieces from one index to a later one: " + from
                                + " " + among);
            }
        }

        /** The numbers of the input the value and the string are made of, each once. */
        public List<NumericTerm> positionsItIsMadeOf() {
            List<NumericTerm> out = new ArrayList<>();
            for (Quantity each : List.of(value, string)) {
                List<NumericTerm> these = switch (each) {
                    case DecisionAtom.OfTheInput(NumericTerm term) -> List.of(term);
                    case WhatAnOperationAnswers answers -> answers.positionsItIsMadeOf();
                    default -> throw new IllegalStateException("held out by the constructor");
                };
                these.stream().filter(term -> !out.contains(term)).forEach(out::add);
            }
            return List.copyOf(out);
        }

        @Override
        public String spelled() {
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("[", value.spelling(), " is among the pieces" + fromSpelled(from)
                    + (among > 0 ? " (the first " + among + ")" : "") + " of "
                    + operation.qualified() + "("
                    + (separator.isPresent() ? "U+" + Integer.toHexString(separator.getAsInt())
                            + ", " : ""), string.spelling(), ")]");
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

        /** The text {@link #spelled} writes, with each term of the dividend held as its own
         *  spelling ({@link NumericTerm#spelling}). */
        @Override
        public Spelling spelling() {
            List<Object> out = new ArrayList<>();
            out.add("floorMod(");
            NumericTerms.entriesInOrder(dividend.coefs()).forEach(each -> {
                out.add((out.size() == 1 ? "" : " + ") + each.getValue().spelled() + "·");
                out.add(each.getKey().spelling());
            });
            if (dividend.constant().signum() != 0) {
                out.add(" + " + dividend.constant().spelled());
            }
            out.add(", " + divisor + ")");
            return Spelling.of(out.toArray());
        }

        @Override
        public String spelled() {
            return spelling().toString();
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What a division of one whole number of the input by another leaves: the remainder of the
     * eaches in a delivery by the pack size a product carries.
     *
     * <p>A number of its own and no form over the two. Fixing the divisor leaves a remainder by a
     * constant of the dividend, whose period is that divisor's, so a rule about the remainder
     * relates the two positions and draws no line on either: where the divisor stands, the
     * dividend that divides by it comes round at a distance it sets. Which values of a position
     * still leave the rule both ways is asked of what the other reaches
     * ({@link souther.compiler.inputs.WhatARelationLeavesUndivided}).
     *
     * <p>The dividend and the divisor are told apart, and two of one position are no relation
     * between two. A divisor of nought stops the run, so no row has a remainder there.
     *
     * @param operation the library's floor remainder that answers it
     * @param dividend  the number divided
     * @param divisor   the number it is divided by
     */
    record RemainderByAnInput(ValueName operation, NumericTerm.FromOnePosition dividend,
                              NumericTerm.FromOnePosition divisor) implements Quantity {

        public RemainderByAnInput {
            if (operation == null || dividend == null || divisor == null
                    || dividend.position().equals(divisor.position())
                    || DefaultBoundOperationFacts.get().divisorOfAFloorRemainder(operation)
                            .isEmpty()) {
                throw new IllegalArgumentException("a remainder by an input is a floor remainder"
                        + " of one number of the input by another of a different position: "
                        + operation + " of " + dividend + " by " + divisor);
            }
        }

        /** Both numbers, the dividend first. */
        public List<NumericTerm.FromOnePosition> operands() {
            return List.of(dividend, divisor);
        }

        @Override
        public String spelled() {
            return "floorMod(" + dividend + ", " + divisor + ")";
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
     * How many different values stand at {@code ofTheOccurrence} over every container inside the
     * elements of the container at {@code container}: each element holds a container of them, and
     * two of them are one value where they are equal, whichever elements hold them.
     *
     * <p>Not a number of the elements: one element holds as many of them as its container does,
     * so it may be more than there are elements, and it is nought where every inner container
     * holds nothing, which a container holding elements may. That is why it is no
     * {@link HowManyDifferent}, which is never more than the elements.
     *
     * @param container       where the elements stand
     * @param ofTheOccurrence a value of each element of a container inside the elements, which is
     *                        one container further in than the elements
     */
    record HowManyDifferentAcross(DecisionSubject container, DecisionSubject ofTheOccurrence)
            implements Quantity {

        public HowManyDifferentAcross {
            if (container == null || ofTheOccurrence == null) {
                throw new IllegalArgumentException("the values are of containers inside elements");
            }
            if (!ofAContainerInside(container, ofTheOccurrence)) {
                throw new IllegalArgumentException(ofTheOccurrence + " is no value of a container"
                        + " inside the elements of " + container);
            }
        }

        /** Whether {@code ofTheOccurrence} is a value of a container inside each element of the
         *  container at {@code container}, one container further in than the elements. */
        public static boolean ofAContainerInside(DecisionSubject container,
                                                 DecisionSubject ofTheOccurrence) {
            return ofTheOccurrence.isAtOrUnder(container.element())
                    && ofTheOccurrence.howManyContainersHoldIt()
                            == container.howManyContainersHoldIt() + 2;
        }

        @Override
        public String spelled() {
            return "#different across " + container + " [" + ofTheOccurrence + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * How many different values a search down the tree at {@code root} collects, where each node
     * it reaches — the root, and the nodes in the lists at {@code through} of every node reached —
     * adds the value at {@code valueAt} of the entry of the map at {@code map} that the key at
     * {@code keyAt} of the node names, and adds nothing where the map holds no entry under it.
     *
     * <p>A number about the nodes the search reaches and the entries their keys pick, so it is no
     * number of the map's entries: an entry no node's key names is not collected, whatever its
     * value. Two nodes naming one entry collect one value, and two entries with one value are one
     * value. Nought exactly where no node reached has an entry.
     *
     * @param root    where the node the search starts from stands
     * @param through the fields of a node the search goes down, each once
     * @param map     where the map the entries are looked up in stands
     * @param keyAt   the fields from a node to the key it looks its entry up by
     * @param valueAt the fields from an entry to the value collected, none for the entry itself
     */
    record HowManyDifferentBelow(TermPath root, List<String> through, TermPath map,
                                 List<String> keyAt, List<String> valueAt) implements Quantity {

        public HowManyDifferentBelow {
            Objects.requireNonNull(root, "a search starts from some node");
            Objects.requireNonNull(map, "entries are looked up in some map");
            through = List.copyOf(through);
            keyAt = List.copyOf(keyAt);
            valueAt = List.copyOf(valueAt);
            if (through.isEmpty()) {
                throw new IllegalArgumentException("a search down a tree goes down some field");
            }
            if (new HashSet<>(through).size() != through.size()) {
                throw new IllegalArgumentException(
                        "a search goes down each field once: " + through);
            }
            if (map.isAtOrUnder(root) || root.isAtOrUnder(map)) {
                throw new IllegalArgumentException(
                        "the map is apart from the tree it is looked up for: " + map + ", " + root);
            }
        }

        /** Where the key a node looks its entry up by stands, taken of the root. */
        public TermPath keyOfTheRoot() {
            TermPath at = root;
            for (String field : keyAt) {
                at = at.then(field);
            }
            return at;
        }

        /** Where the value collected of an entry stands, taken of the entries of the map. */
        public TermPath valueOfAnEntry() {
            TermPath at = map.element();
            for (String field : valueAt) {
                at = at.then(field);
            }
            return at;
        }

        @Override
        public String spelled() {
            return "#different below " + root + " through " + through + " [" + map + "["
                    + keyAt + "]" + valueAt + "]";
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * Where the value of an element a count of different values counts once stands: at one place
     * of every element, or at the place the element's case chooses.
     *
     * <p>Two elements are one value where the values they hold there are equal, whichever place
     * each was read at: a fold filing each case under a field of its own files a receipt and a
     * stocktake of one {@code sku} under one key.
     */
    sealed interface TheValue {

        /**
         * Where the value stands as far as which containers hold it goes: the place itself, or the
         * element whose case chooses the place, which stands inside the same containers.
         */
        DecisionSubject where();

        /** Every place of the input it reads to tell the value: the place, or the place the case
         *  is told at and the place each case reads. */
        List<TermPath> places();

        /** Every place the value itself is held at: the place, or the place each case reads. */
        List<TermPath> heldAt();

        /** Whether this is the value at {@code place} of every element. */
        default boolean isAt(TermPath place) {
            return this instanceof AtAPlace(DecisionSubject.AnInput(TermPath at))
                    && at.equals(place);
        }

        /** Whether some place the value is held at is {@code path}, inside it or holds it. */
        default boolean overlaps(TermPath path) {
            return heldAt().stream().anyMatch(at -> at.isAtOrUnder(path) || path.isAtOrUnder(at));
        }

        /** Whether {@code key}, read from the elements at {@code elements}, is where this
         *  stands. */
        default boolean isWhereFiled(ElementKey key, TermPath elements) {
            return switch (key) {
                case ElementKey.At(ElementProjection way) -> isAt(way.from(elements));
                case ElementKey.ByCase chosen -> this instanceof ChosenByCase(
                        TermPath of, ElementKey.ByCase same)
                        && of.equals(elements) && same.equals(chosen);
            };
        }

        /** How it is written. */
        String spelled();

        /** The value at {@code at}. */
        record AtAPlace(DecisionSubject at) implements TheValue {

            public AtAPlace {
                Objects.requireNonNull(at, "a value stands somewhere");
            }

            @Override
            public DecisionSubject where() {
                return at;
            }

            @Override
            public List<TermPath> places() {
                return at instanceof DecisionSubject.AnInput(TermPath path) ? List.of(path)
                        : List.of();
            }

            @Override
            public List<TermPath> heldAt() {
                return places();
            }

            @Override
            public String spelled() {
                return at.spelled();
            }

            @Override
            public String toString() {
                return spelled();
            }
        }

        /**
         * The value at the place of the element at {@code element} that its case chooses, as
         * {@code key} reads it ({@link ElementKey.ByCase}).
         *
         * @param element where the element stands, a position of the input
         * @param key     the ways from the element, one for each case of it
         */
        record ChosenByCase(TermPath element, ElementKey.ByCase key) implements TheValue {

            public ChosenByCase {
                Objects.requireNonNull(element, "the element whose case chooses stands somewhere");
                Objects.requireNonNull(key, "a case chooses among ways");
            }

            @Override
            public DecisionSubject where() {
                return new DecisionSubject.AnInput(element);
            }

            @Override
            public List<TermPath> places() {
                List<TermPath> out = new ArrayList<>();
                key.reads().forEach(way -> out.add(way.from(element)));
                return out.stream().distinct().sorted(Comparator.comparing(TermPath::toString))
                        .toList();
            }

            @Override
            public List<TermPath> heldAt() {
                return key.ways().stream().map(way -> way.from(element)).toList();
            }

            @Override
            public String spelled() {
                return key.spelledFrom(element);
            }

            @Override
            public String toString() {
                return spelled();
            }
        }
    }

    /**
     * How many different values stand at {@code ofTheElement} over the elements of the container
     * at {@code container}: the element itself, a position inside it, the key it is filed under, or
     * the place its case chooses — two of them one value where they are equal. Never more than the
     * container holds, and nought exactly where it holds nothing.
     *
     * <p>A number about every pair of elements and not about each: whether one adds to it turns on
     * the ones beside it, so it is no count of elements meeting something.
     */
    record HowManyDifferent(DecisionSubject container, TheValue ofTheElement)
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

        /** Whether {@code ofTheElement} is one value of each element of the container at
         *  {@code container}, as {@link #oneOfEach(DecisionSubject, DecisionSubject)} has the place
         *  it stands at; one its case chooses is the element's own. */
        public static boolean oneOfEach(DecisionSubject container, TheValue ofTheElement) {
            return switch (ofTheElement) {
                case TheValue.AtAPlace(DecisionSubject at) -> oneOfEach(container, at);
                case TheValue.ChosenByCase chosen ->
                        container.element().equals(chosen.where());
            };
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
     * How many different values stand at {@code ofTheElement} over the elements of the container
     * at {@code container} that {@code meeting} keeps: the values of {@link HowManyDifferent}, of
     * the elements meeting a statement alone.
     *
     * <p>A number of the classes of elements one value at {@code ofTheElement} makes, and not of
     * the elements: two elements meeting the statement with one value there add one. So it is no
     * {@link HowManyMeet}, which counts each element that meets it.
     *
     * <p>What the statement is asked of is part of which number this is. Asked of each element, a
     * value is counted where some element holding it meets the statement. Asked of each value, it
     * is a statement about what the elements holding that value come to, which every one of them
     * answers alike, so a value is counted where its elements do; {@code amount > 0} asked of each
     * element and the total of the amounts under a value above nought are two numbers, and
     * {@code 10} and {@code -10} under one value tell them apart.
     *
     * <p>The elements counted are the container's own, or every element of the containers inside
     * its elements put end to end ({@link #across}), as a flattening has them: two of those holding
     * one value are one value whichever containers hold them, so the number is no sum of a number
     * of each inner container. Which of the two it is, is where {@code ofTheElement} stands.
     *
     * @param container    where the elements stand, or the elements holding the containers they
     *                     stand in
     * @param ofTheElement one value of each element, as {@link HowManyDifferent#oneOfEach} has it,
     *                     of the container's elements or of the elements of a container inside
     *                     each of them
     * @param meeting      what keeps an element or a value, and which of the two it is asked of
     */
    record HowManyDifferentMeet(DecisionSubject container, TheValue ofTheElement,
                                Selection meeting) implements Quantity {

        public HowManyDifferentMeet {
            if (container == null || ofTheElement == null || meeting == null) {
                throw new IllegalArgumentException("the values are of the elements of a container"
                        + " meeting something");
            }
            String not = whyNot(container, ofTheElement, meeting);
            if (not != null) {
                throw new IllegalArgumentException(not);
            }
        }

        /**
         * How many different values stand at {@code ofTheElement} over the elements of the
         * container at {@code container} that {@code meeting} keeps — or null where that is no
         * such number, as the constructor would refuse it.
         */
        public static HowManyDifferentMeet of(DecisionSubject container, TheValue ofTheElement,
                                              Selection meeting) {
            return whyNot(container, ofTheElement, meeting) == null
                    ? new HowManyDifferentMeet(container, ofTheElement, meeting) : null;
        }

        /**
         * Why these are no such number, or null where they are one: the value is one of each
         * element, the statement keeps some elements and not others, quantifies none of them
         * again, is read through and answers on each, and asked of each value it answers alike for
         * the elements holding one.
         */
        private static String whyNot(DecisionSubject container, TheValue ofTheElement,
                                     Selection meeting) {
            Proposition stated = meeting.statement();
            DecisionSubject counted = HowManyDifferent.oneOfEach(container, ofTheElement)
                    ? container : inside(container, ofTheElement);
            if (counted == null) {
                return ofTheElement + " is no one value of each element of " + container
                        + ", or of a container inside each";
            }
            if (!stated.mayTurnOnAnElementOf(counted)) {
                return "what keeps the elements of " + counted + " is the same for each of"
                        + " them: " + stated;
            }
            if (Proposition.Some.quantifiesOver(counted, stated)
                    || Proposition.Some.quantifiesOver(container, stated)) {
                return "what keeps an element of " + counted + " quantifies them again, which"
                        + " would read two elements as one: " + stated;
            }
            if (Proposition.mayAnswerNothing(stated)) {
                return "the elements are kept by a statement answering on every one of them: "
                        + stated;
            }
            if (Proposition.leavesSomethingUnread(stated)) {
                return "the elements are kept by a statement read through, and " + stated
                        + " was not";
            }
            if (meeting instanceof Selection.OfEachValue
                    && !Selection.OfEachValue.answersAlike(container, ofTheElement, stated)) {
                return stated + " is asked of each value at " + ofTheElement + ", and reads"
                        + " something of an element that the other elements holding its value"
                        + " need not hold";
            }
            return null;
        }

        /**
         * The container inside each element of the input's container at {@code container} that
         * {@code ofTheElement} is one value of each element of, or null where it is none such.
         */
        private static DecisionSubject inside(DecisionSubject container, TheValue ofTheElement) {
            DecisionSubject where = ofTheElement.where();
            if (!(container instanceof DecisionSubject.AnInput)
                    || !(where instanceof DecisionSubject.AnInput(TermPath at))
                    || !HowManyDifferentAcross.ofAContainerInside(container, where)) {
                return null;
            }
            DecisionSubject inner = new DecisionSubject.AnInput(
                    at.containersHoldingIt().getLast());
            return HowManyDifferent.oneOfEach(inner, ofTheElement) ? inner : null;
        }

        /**
         * Whether the elements counted are those of the containers inside the elements of
         * {@link #container}, all of them put end to end, rather than its own.
         */
        public boolean across() {
            return !HowManyDifferent.oneOfEach(container, ofTheElement);
        }

        /**
         * Where the elements the statement is asked of stand: the container's own, or, where the
         * count is {@link #across} them, the container inside each of its elements.
         */
        public DecisionSubject occurrences() {
            return across() ? inside(container, ofTheElement) : container;
        }

        /**
         * How many of the elements meet what keeps them, each counted however many hold its
         * value: the count whose elements this counts the values of, and what one element meeting
         * the statement is asked whatever is counted of them. Across the containers inside the
         * elements, of the elements of one of them.
         */
        public HowManyMeet elementsMeetingIt() {
            return new HowManyMeet(occurrences(), meeting.statement());
        }

        /**
         * What keeps an element or a value of {@link HowManyDifferentMeet}, and which of the two
         * it is asked of.
         */
        public sealed interface Selection {

            /** The statement, over the element's own numbers, the input's, and, asked of a value,
             *  what the elements holding it come to. */
            Proposition statement();

            /** {@code stated} asked of what this one is asked of. */
            default Selection askedAgainOf(Proposition stated) {
                return switch (this) {
                    case OfEachElement _ -> new OfEachElement(stated);
                    case OfEachValue _ -> new OfEachValue(stated);
                };
            }

            /**
             * Asked of each element: a value is counted where some element holding it meets the
             * statement, whatever the others holding it do.
             */
            record OfEachElement(Proposition statement) implements Selection {

                public OfEachElement {
                    Objects.requireNonNull(statement, "an element is kept by some statement");
                }
            }

            /**
             * Asked of each value: of what the elements holding it come to, which is one answer for
             * all of them, so the value is counted where its elements meet it.
             */
            record OfEachValue(Proposition statement) implements Selection {

                public OfEachValue {
                    Objects.requireNonNull(statement, "a value is kept by some statement");
                }

                /**
                 * Whether {@code stated} reads nothing of an element of the container at
                 * {@code container} but its value at {@code ofTheElement} and what the elements
                 * holding that value come to: every number it reads inside an element is the value
                 * itself, how often it occurs ({@link NumericTerm.Multiplicity}) or one gathered
                 * under it, of every element ({@link NumericTerm.GatheredUnderItsKey}), and every
                 * place inside an element it reads is the value's or one such a number is read
                 * from.
                 *
                 * <p>Where the value is of the elements of a container inside each element of
                 * {@code container}, a number gathered under it is of every element of all of those
                 * ({@link NumericTerm.GatheredUnderItsKey} is a number of the run), and a place of
                 * the element of {@code container} holding one is no place the others holding the
                 * value share: it is outside the elements only where it is outside that one too.
                 */
                public static boolean answersAlike(DecisionSubject container,
                                                   TheValue ofTheElement, Proposition stated) {
                    if (!(container instanceof DecisionSubject.AnInput(TermPath held))
                            || !(ofTheElement.where() instanceof DecisionSubject.AnInput(
                                    TermPath where))) {
                        return false;
                    }
                    TermPath element = switch (ofTheElement) {
                        case TheValue.AtAPlace _ -> where.containersHoldingIt().getLast()
                                .element();
                        case TheValue.ChosenByCase chosen -> chosen.element();
                    };
                    return alike(stated, new Apart(element, held.element(), ofTheElement));
                }

                /**
                 * The element a value is of, the element of the container counted over that holds
                 * it — the same element where the value is of the container's own — and the
                 * value.
                 */
                private record Apart(TermPath element, TermPath outermost, TheValue value) {

                    /** Whether {@code at} is the value itself, which one place is only where the
                     *  value stands at one place of every element. */
                    boolean isTheValue(TermPath at) {
                        return value.isAt(at);
                    }

                    /** Whether {@code key}, read from the elements, is where the value stands. */
                    boolean filesUnderIt(ElementKey key) {
                        return value.isWhereFiled(key, element);
                    }
                }

                /**
                 * Whether {@code stated} answers alike for every element holding one value, by
                 * what each kind of statement is: proved of each kind that is, and refused of
                 * every other. Which places a statement reads is not enough — which element
                 * holding a value is the last to, as {@link Proposition.LastToHold} states, reads
                 * no place but the value's and turns on which element it is.
                 */
                private static boolean alike(Proposition stated, Apart apart) {
                    return switch (stated) {
                        case Proposition.Always _ -> true;
                        case Proposition.Compared compared -> switch (compared.relation()) {
                            case Relation.Affine affine -> affine.form().coefs().keySet()
                                    .stream().allMatch(each -> alike(each, apart));
                            case Relation.Ordered ordered -> alike(ordered.term(), apart);
                        };
                        case Proposition.All _, Proposition.Any _, Proposition.WhereItAnswers _,
                             Proposition.SoManyHold _, Proposition.OfTheWays _ ->
                                stated.partsHeld().stream()
                                .allMatch(part -> alike(part, apart));
                        case Proposition.Truth truth -> alike(truth.of(), apart);
                        case Proposition.Present present -> alike(present.of(), apart);
                        case Proposition.InCases cases -> alike(cases.of(), apart);
                        case Proposition.SameValue same ->
                                alike(same.one(), apart) && alike(same.other(), apart);
                        case Proposition.StringInside inside ->
                                alike(inside.inner(), apart) && alike(inside.outer(), apart);
                        // Which element holding the value is the last to, what some element of a
                        // container meets, what an operation answered of something: each turns on
                        // which element it is asked of, or on what nothing here reads. And which
                        // strings a string is one of, which no model has been shown to ask of the
                        // element a value is held by.
                        case Proposition.LastToHold _, Proposition.Some _,
                             Proposition.OnAnApplication _, Proposition.SomeReachable _,
                             Proposition.Unread _, Proposition.Carried _,
                             Proposition.InTheStrings _ -> false;
                    };
                }

                /** Whether {@code subject} is the value itself or a place of the input outside
                 *  the elements. */
                private static boolean alike(DecisionSubject subject, Apart apart) {
                    return subject instanceof DecisionSubject.AnInput(TermPath at)
                            && (apart.isTheValue(at) || !at.isAtOrUnder(apart.outermost()));
                }

                /** Whether {@code number} is the value itself, how often it occurs among the
                 *  elements of one container, one gathered under it of every element, or a number
                 *  of the input outside the elements. */
                private static boolean alike(Quantity number, Apart apart) {
                    if (!(number instanceof DecisionAtom.OfTheInput(NumericTerm term))) {
                        return false;
                    }
                    if (term instanceof NumericTerm.Multiplicity often) {
                        return apart.element().equals(apart.outermost())
                                && often.container().element().equals(apart.element())
                                && apart.isTheValue(often.place());
                    }
                    if (term instanceof NumericTerm.GatheredUnderItsKey gathered) {
                        return gathered.elements().equals(apart.element())
                                && gathered.selection() == null
                                && apart.filesUnderIt(gathered.key());
                    }
                    return (term instanceof NumericTerm.ValueOf(TermPath at)
                            && apart.isTheValue(at))
                            || !term.subjectPath().isAtOrUnder(apart.outermost());
                }
            }
        }

        @Override
        public String spelled() {
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("#different " + container + " [" + ofTheElement + "] where "
                    + (meeting instanceof Selection.OfEachValue ? "each value " : "") + "[",
                    meeting.statement().spelling(), Spelling.CLOSE);
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
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("#sum " + container + " [", ofTheElement.spelling(), Spelling.CLOSE);
        }

        @Override
        public String toString() {
            return spelled();
        }
    }

    /**
     * What a total over a container the body wrote out adds up to, or how many that container
     * holds, in the ways its elements are kept, read once for all of them: a stand-in that
     * {@link GivenTotals} replaces by the total of each way.
     *
     * <p>It never reaches a reader. A comparison read over it states the same thing in every way
     * but for what the total is, and the derivation that gives each way its total concludes the
     * statement with the stand-in taken out.
     *
     * @param reading which reading of a comparison it stands in, so that two totals of two
     *                readings are two quantities
     * @param counted whether it is how many the container holds, and not what it adds up to
     */
    record TheKeptTotal(int reading, boolean counted) implements Quantity {

        /** What a reader that is handed the stand-in has been given wrongly. */
        public IllegalStateException reachedAReader() {
            return new IllegalStateException("a total of the elements a way keeps is given its"
                    + " ways before a reader is handed it: " + this);
        }

        @Override
        public String spelled() {
            return (counted ? "#kept-count " : "#kept-sum ") + reading;
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
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            List<Spelling> pieces = new ArrayList<>(2 * each.size() + 1);
            pieces.add(Spelling.of("#["));
            for (int i = 0; i < each.size(); i++) {
                if (i > 0) {
                    pieces.add(Spelling.SEPARATOR);
                }
                pieces.add(each.get(i).spelling());
            }
            pieces.add(Spelling.CLOSE);
            return Spelling.joined(pieces);
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
    record HowManyMeet(DecisionSubject container, Proposition ofTheElement)
            implements Quantity, ReadAlongAContainer {

        public HowManyMeet {
            if (container == null || ofTheElement == null) {
                throw new IllegalArgumentException("a count is of the elements of some container");
            }
            if (!ofTheElement.mayTurnOnAnElementOf(container)) {
                throw new IllegalArgumentException("a count of " + ofTheElement
                        + " is the same for every element of " + container);
            }
            // Said of each element, as some element meeting it is ({@link #someMeets}).
            if (Proposition.Some.quantifiesOver(container, ofTheElement)) {
                throw new IllegalArgumentException("a count of the elements of " + container
                        + " is of a statement quantifying them again, which would read two"
                        + " elements as one: " + ofTheElement);
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
            return spelling().toString();
        }

        @Override
        public Spelling spelling() {
            return Spelling.of("#" + container + " [", ofTheElement.spelling(), Spelling.CLOSE);
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
     * {@link #spelled}, held as the pieces it is put together from ({@link Spelling}).
     *
     * <p>A count of a statement is spelled with the statement's spelling in it, and a comparison
     * over the count is told apart and ordered by its own spelling — so a quantity that wrote the
     * statement out would hold its text again in every comparison it stands in, and again in every
     * count of a statement such a comparison is part of. A quantity made of statements or of other
     * quantities holds their spellings themselves; one made of neither is its text.
     */
    default Spelling spelling() {
        return Spelling.of(spelled());
    }

    /**
     * What a walk over the elements of a container hands its step beside the element, where that
     * says where a value bound in the step lies and which of those values it takes: the end kept
     * so far of what it carried, or where the element stands.
     *
     * <p>One type for every such thing, so a reader that carries one carries all of them, and one
     * that asks which it is answers each.
     */
    public sealed interface HandedToTheStep extends ReadOffABinding
            permits KeptSoFar, PositionInTheWalk {}

    /**
     * What a binding's value is read off a container's elements as: what a walk hands its step, or
     * the element an index written down picks.
     */
    public sealed interface ReadOffABinding extends ReadAlongAContainer
            permits HandedToTheStep, PickedAtAnIndex {}

    /**
     * A number read off a container's elements one by one and at no one position of the input,
     * where what it is says where it lies beside how many the container holds: what a walk hands
     * its step, the element an index picks, or how many of the elements meet a statement.
     *
     * <p>One type for every such thing, for the reason {@link HandedToTheStep} is one: a reader of
     * a relation carrying one carries all of them.
     */
    public sealed interface ReadAlongAContainer permits ReadOffABinding, HowManyMeet {}

    /**
     * The element at {@code index} of {@code container}, which a name an arm opening a lookup at
     * that index binds.
     *
     * <p>The element and not the elements. Where the elements of the container stand is one place
     * ({@link TermPath.Step.Element}) and a row puts a value at all of them or at some, so a number
     * read at that place says nothing of which element a comparison is about: the index is what
     * does, and it is held here beside the place whose declarations and rules the element is read
     * under, which is a different thing and is not to be taken for it. A reader that wants the
     * values the element may take asks the place; one that wants a value at the element asks for a
     * container of more than {@code index} elements.
     *
     * @param container the list the lookup is made in, which no other container holds
     * @param index     the index written down
     * @param element   where the elements of the container stand, or a field under them where the
     *                  name is read through one: the place the element's declarations are read at
     * @param howMany   how many the container holds
     */
    record PickedAtAnIndex(TermPath container, long index, TermPath element,
                           NumericTerm.FromOnePosition howMany) implements ReadOffABinding {

        public PickedAtAnIndex {
            Objects.requireNonNull(container, "an element of some container");
            Objects.requireNonNull(element, "and the place the elements stand at");
            if (index < 0 || container.insideAContainer()
                    || !element.isAtOrUnder(container.element())
                    || !PositionInTheWalk.counts(howMany, container)) {
                throw new IllegalArgumentException("an element is picked at an index of a"
                        + " container that no other holds, and read where its elements stand: "
                        + container + "[" + index + "] at " + element);
            }
        }
    }

    /**
     * Where the element a walk over every element of {@code container} hands its step stands in
     * it, counted from nought in the order the container holds its elements: how many elements
     * come before it.
     *
     * <p>So beside how many the container holds it lies from nought to one below that, and a run
     * of a container of so many hands its step each of those values once — every one of them, in
     * every row, since the walk is over every element. A container holding nothing hands the step
     * nothing, and no value bound in it is read there.
     *
     * @param container the container the walk walks, which no other container holds
     * @param howMany   how many the container holds
     */
    record PositionInTheWalk(TermPath container, NumericTerm.FromOnePosition howMany)
            implements HandedToTheStep {

        public PositionInTheWalk {
            Objects.requireNonNull(container, "a walk walks some container");
            if (container.insideAContainer()) {
                throw new IllegalArgumentException("a position is counted in one container, and `"
                        + container + "` is one of many");
            }
            if (!counts(howMany, container)) {
                throw new IllegalArgumentException("a position is counted against how many the"
                        + " container holds: " + howMany + " of " + container);
            }
        }

        /** Whether {@code howMany} is how many the value at {@code container} holds, as it
         *  stands. */
        public static boolean counts(NumericTerm howMany, TermPath container) {
            return howMany instanceof NumericTerm.TakenOf count
                    && count.takenAs() instanceof TakenAs.HowManyItHolds
                    && count.position().equals(container)
                    && count.transformation() instanceof ValueTransformation.Identity;
        }
    }

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
                     NumericTerm.FromOnePosition ofEach, NumericTerm.FromOnePosition howMany)
            implements HandedToTheStep {

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
            if (seed instanceof Seed.OfTheKey(var key, var _) && Seed.OfTheKey.holdsTheNumber(
                    key, ofEach)) {
                throw new IllegalArgumentException("the elements of one key hold one number,"
                        + " and what was kept of them is no other value: " + key + " and "
                        + ofEach);
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
             * @param reachedBy the arm of the match on a lookup of the key that finds the end,
             *                  which is entered only where an earlier element has the key — or
             *                  none where the walk hands a closure the value found. The name
             *                  already tells this end from the end found by another expansion of
             *                  the same code, and so does this
             */
            record OfTheKey(TermPath key, Optional<EnteredArm> reachedBy)
                    implements Seed {

                public OfTheKey {
                    Objects.requireNonNull(key, "a key stands somewhere in an element");
                    Objects.requireNonNull(reachedBy, "an arm, or none");
                }

                /**
                 * Whether the key and the number are one place, or one holds the other. Elements
                 * with the same key then hold the same number, so the end kept of the earlier ones
                 * is the number of the one compared and no value beside it.
                 */
                public static boolean holdsTheNumber(TermPath key,
                                                     NumericTerm.FromOnePosition number) {
                    return number.placesReadOff().stream()
                            .anyMatch(place -> place.isAtOrUnder(key) || key.isAtOrUnder(place));
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
     * <p>Where the value is what a walk hands its step beside the element, what the walk hands is
     * carried beside it ({@link HandedToTheStep}): which end the walk kept of what it carried, or
     * where the element stands. That says where the value may lie and which of those values it is shown to
     * take, and still nothing of which value it is on a run.
     *
     * @param binding which binding names the value
     * @param steps   the steps read off it that go somewhere, outermost first
     * @param type    what stands there, which is how its numbers are spaced
     * @param madeOf  why what the value was made from is no number of the input, where the
     *                reading met it and stopped
     * @param handed  what a walk hands its step, where the value is that
     */
    record OfABinding(BindingId binding, List<TermPath.Step> steps, Type type,
                      Optional<WhyUnread> madeOf, Optional<ReadOffABinding> handed)
            implements Quantity {

        public OfABinding {
            if (binding == null || type == null || madeOf == null || handed == null) {
                throw new IllegalArgumentException("a bound number is some binding's, of some type");
            }
            steps = List.copyOf(steps);
            if (handed.isPresent() && (madeOf.isPresent()
                    || (!steps.isEmpty() && !(handed.get() instanceof PickedAtAnIndex)))) {
                throw new IllegalArgumentException("what a walk hands its step is the value itself,"
                        + " and nothing of it was read to stop: " + binding);
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
