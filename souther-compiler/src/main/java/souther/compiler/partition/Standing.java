package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.NumericTerms;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.WholeNumberRuns;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What a row has to satisfy to stand at one coverage item, in the words a search can solve.
 *
 * <p><b>The solver's input language, and not a second listing of the quantities.</b> What these name
 * is the kind of constraint a search has to answer — one position pinned or confined, two positions
 * held a fixed distance apart, a form held at a value — and a quantity added later adds one of these
 * only where it needs a kind of search that is not here. A quantity whose items lower onto a
 * constraint that already exists brings no new shape.
 *
 * <p>Which is why this is apart from {@link BorderQuantity}. What a border means and how a row at one
 * of its points is found are two questions; answered by one type, every reader that only wanted the
 * first was holding the second, and the search that answers the second was written once per shape of
 * line.
 *
 * <p>Nothing here holds what the rules leave. The region a row has to be written inside is the
 * caller's — it comes from the reading of the declarations and is the same for every item of a
 * behavior — so a constraint is what the <em>border</em> asks and is handed to {@link LevelRealizer}
 * beside what the model admits.
 */
public sealed interface Standing {

    /**
     * This, where {@code way} asks of the numbers it is at what the search for a row chooses
     * among: a row composed at what the way turns away is one no row along it is. Itself where
     * the way asks nothing such of it.
     */
    default Standing alongTheWay(Reachability.Reaching way) {
        return this;
    }

    /**
     * This, where a row is a witness of the item only inside {@code decides}, the case the line
     * decides in: what the case says of the item's own quantity narrows where a row is composed.
     * Never narrower than what every row meeting the case is at.
     */
    default Standing inTheCase(Proposition decides) {
        return this;
    }

    /**
     * What one whole number of a row leaves of another divided by it, at a remainder or in a run of
     * them.
     *
     * <p>A row at a remainder is a divisor that can leave it and a dividend that is that remainder
     * more than a whole number of turns of the divisor: the divisor is fixed first, at a value
     * whose size is above the remainder's and whose sign is the remainder's where it has one, and
     * the dividend is then held to a class of values, a constraint the search already answers.
     * Which divisors are tried is the search's walk over those the rules leave; the remainder is
     * the item.
     *
     * @param dividend the number divided
     * @param divisor  the number it is divided by
     * @param on       the order each number stands on
     * @param levels   the remainders it can leave, which is what the criterion is about
     */
    record OfARemainderByAnInput(NumericTerm.FromOnePosition dividend,
                                 NumericTerm.FromOnePosition divisor, Map<NumericTerm, Carrier> on,
                                 LevelSpace levels, Criterion where) implements Standing {

        public OfARemainderByAnInput {
            on = Map.copyOf(on);
            if (dividend == null || divisor == null || dividend.equals(divisor)
                    || !on.keySet().equals(Set.of(dividend, divisor))) {
                throw new IllegalArgumentException("a remainder by an input is of two numbers,"
                        + " each on one order: " + dividend + " by " + divisor + " against "
                        + on.keySet());
            }
        }
    }

    /**
     * What two whole numbers of a row come to multiplied, at a value of the product or in a run of
     * them.
     *
     * <p>A row at a level is a pair whose product is the level, so one factor is fixed at a value
     * that divides it and the other is held where the level over that value is: a form of one
     * number, which is a constraint the search already answers. Which value of the first is fixed
     * is the search's walk over what divides the level; the product is the item.
     *
     * @param one    the factor fixed first
     * @param other  the factor the level is then a form of
     * @param on     the order each factor stands on
     * @param levels the values the product takes, which is what the criterion is about
     */
    record OfAProduct(NumericTerm.FromOnePosition one, NumericTerm.FromOnePosition other,
                      Map<NumericTerm, Carrier> on, LevelSpace levels, Criterion where)
            implements Standing {

        public OfAProduct {
            on = Map.copyOf(on);
            if (one == null || other == null || one.equals(other)
                    || !on.keySet().equals(Set.of(one, other))) {
                throw new IllegalArgumentException("a product is of two numbers, each on one"
                        + " order: " + one + " and " + other + " against " + on.keySet());
            }
        }
    }

    /**
     * One position's own value, at a level of its carrier or anywhere in a side of it.
     *
     * <p>The whole of what a border on one coordinate asks. Which of the two it is is the criterion's
     * to say, and both are answered by the same search: a place the carrier names that the criterion
     * accepts.
     */
    record OfOneCoordinate(NumericTerm.FromOnePosition term, Carrier of, Criterion where)
            implements Standing {}

    /**
     * Two positions on one carrier, standing the criterion's number of that carrier's steps apart.
     *
     * <p>Both are fixed at once, which is the whole of what makes the row one on the line. A search
     * that settled one and left the other to its own range would produce a row beside the line as
     * readily as one on it.
     *
     * <p>The place they are apart <em>from</em> is not here. Where the line is is a relation the row
     * satisfies and the pair a search happens to find is a witness rather than the item: written
     * here, one row on the line would name every other row on it a different item.
     */
    record OfTwoOnOneCarrier(NumericTerm.FromOnePosition on, NumericTerm.FromOnePosition against,
                             Carrier of, Criterion where)
            implements Standing {

        public OfTwoOnOneCarrier {
            // Two positions, which is what makes this a distance. One position named twice stands
            // nowhere from itself, and a reader working the quantity out of the pair gets a form
            // weighing no term — a question about nothing, arriving where an answer about a
            // quantity belongs.
            if (on != null && on.equals(against)) {
                throw new IllegalArgumentException(
                        "a distance is between two positions, and this names one twice: " + on);
            }
        }
    }

    /**
     * An arithmetic form over several positions, held at a value of the form or past one.
     *
     * <p>The one constraint here that has to be searched for. A level of a form is reached by many
     * assignments and by none, and which it is depends on what every rule leaves each position — so
     * this names the equation and the caller hands in the box.
     *
     * <p>The order the form's own values sit on comes with it. Which levels a form takes is the
     * quantity's answer, and a search that worked it out again from the coefficients would be the
     * quantity's reading written a second time, free to disagree with it about where the next level
     * is.
     *
     * <p>And an order per position beside it. Which order a position is read and written on is a
     * question about that position, and a form may be over positions that answer it differently —
     * handed one order for all of them, a search walked every position over the values of whichever
     * order it was given.
     */
    record OfAForm(souther.compiler.numeric.LinearForm<NumericTerm> form,
                   java.util.Map<NumericTerm, Carrier> on, LevelSpace levels, Criterion where)
            implements Standing {

        public OfAForm {
            on = java.util.Map.copyOf(on);
            // A form over no position comes to its constant wherever a row stands, so there is
            // nothing to search for and nothing for a region to be asked about.
            if (form.coefs().isEmpty()) {
                throw new IllegalArgumentException(
                        "a form stands over the positions it names, and this names none: " + form);
            }
            if (!on.keySet().equals(form.coefs().keySet())) {
                throw new IllegalArgumentException("a form stands over the positions it names, each"
                        + " on one order: "
                        + NumericTerms.inOrder(form.coefs().keySet())
                        + " against " + NumericTerms.inOrder(on.keySet()));
            }
        }
    }

    /**
     * What a division by a written number leaves of a form of several positions, at a remainder or
     * in a run of them.
     *
     * <p>The form is held at some value that leaves it, and which value that is a search over the
     * form's own values: every one of the class the remainder and the divisor name, that the rules
     * leave the form room for. The remainders are the item and the values of the form are how a row
     * gets to one of them, so two rows at one remainder by two values of the form are one item.
     *
     * @param dividend   the form the division is of, with the constant it is moved by
     * @param on         the order each number of the form stands on
     * @param levels     the remainders it can leave, which is what the criterion is about
     * @param divisor    the number it is divided by, above nought
     * @param remainders the remainders a row is composed at: every one, or those a way to the
     *                   item leaves ({@link #alongTheWay})
     */
    record OfARemainder(LinearForm<NumericTerm> dividend, Map<NumericTerm, Carrier> on,
                        LevelSpace levels, BigInteger divisor, WholeNumberRuns remainders,
                        Criterion where) implements Standing {

        public OfARemainder {
            on = Map.copyOf(on);
            if (dividend.coefs().isEmpty() || !on.keySet().equals(dividend.coefs().keySet())
                    || divisor.signum() <= 0 || remainders == null) {
                throw new IllegalArgumentException("a remainder is of a form over the numbers it"
                        + " names, each on one order, and by a divisor above nought: " + dividend
                        + " against " + on.keySet() + " by " + divisor);
            }
        }

        /** At every remainder the divisor leaves. */
        public OfARemainder(LinearForm<NumericTerm> dividend, Map<NumericTerm, Carrier> on,
                            LevelSpace levels, BigInteger divisor, Criterion where) {
            this(dividend, on, levels, divisor, OfARemainderAndAForm.every(divisor), where);
        }

        /**
         * At the remainders {@code way} leaves this remainder as well, as
         * {@link OfARemainderAndAForm#alongTheWay} narrows its own: a row composed at another is one
         * the way turns away.
         *
         * <p>A remainder the way asks of a form that is this one moved by a constant, by the same
         * divisor, is this remainder moved by the difference of the two constants, turned round the
         * divisor; what that leaves of the way's remainders is what it leaves of this one. One by
         * another divisor, or of another form, says nothing of this remainder alone and is left for
         * the row to be read against.
         */
        @Override
        public Standing alongTheWay(Reachability.Reaching way) {
            WholeNumberRuns left = remainders;
            for (OnTheWay.TakenIn cut : way.boundedOnTheWay()) {
                if (cut.demand() instanceof RowDemand.OnARemainder asked
                        && asked.dividend().coefs().equals(dividend.coefs())
                        && asked.remainder().divisor().equals(divisor)
                        && asked.dividend().constant().isWhole() && dividend.constant().isWhole()) {
                    BigInteger moved = whole(asked.dividend().constant())
                            .subtract(whole(dividend.constant()));
                    left = left.and(turnedBack(asked.leaves(), moved, divisor));
                }
            }
            return left.equals(remainders) ? this
                    : new OfARemainder(dividend, on, levels, divisor, left, where);
        }

        /**
         * At the remainders the case the line decides in may hold at as well
         * ({@link ResiduesAStatementLeaves}): a row at another is one the line decides nothing
         * at, which a point of it asks for no row of.
         */
        @Override
        public Standing inTheCase(Proposition decides) {
            WholeNumberRuns left = remainders.and(
                    ResiduesAStatementLeaves.of(decides, dividend, divisor));
            return left.equals(remainders) ? this
                    : new OfARemainder(dividend, on, levels, divisor, left, where);
        }

        /**
         * The remainders of this form whose remainder moved by {@code moved} is among {@code runs}:
         * each run turned back by {@code moved} round {@code divisor}, a run that crosses nought
         * taken as the two it comes to.
         */
        static WholeNumberRuns turnedBack(WholeNumberRuns runs, BigInteger moved,
                                          BigInteger divisor) {
            WholeNumberRuns every = OfARemainderAndAForm.every(divisor);
            WholeNumberRuns out = WholeNumberRuns.NONE;
            for (WholeNumberRuns.Run run : runs.and(every).runs()) {
                BigInteger from = run.from().subtract(moved).mod(divisor);
                BigInteger to = run.to().subtract(moved).mod(divisor);
                out = out.or(from.compareTo(to) <= 0 ? WholeNumberRuns.one(from, to)
                        : WholeNumberRuns.one(from, divisor.subtract(BigInteger.ONE))
                                .or(WholeNumberRuns.one(BigInteger.ZERO, to)));
            }
            return out;
        }

        private static BigInteger whole(ExactRatio ratio) {
            return ((ExactAnswer.Held<BigInteger>) ratio.floor()).value();
        }
    }

    /**
     * What a division by a written number leaves of a form of several positions, together with
     * what a form of other positions comes to, at a level of the two added up.
     *
     * <p>Two things a row has to be at: the form leaving a remainder, and the other numbers
     * standing where they add up to what the level leaves of that remainder. Neither is the item
     * alone. The two forms name no position in common, so the remainder is chosen and the added
     * numbers are met against what it leaves.
     *
     * @param dividend   the form the division is of, with the constant it is moved by
     * @param on         the order each number of the dividend stands on
     * @param divisor    the number it is divided by, above nought
     * @param remainders the remainders a row is composed at: every one, or those a way to the
     *                   item leaves ({@link #alongTheWay})
     * @param added      what is added to the remainder, with no constant
     * @param addedOn    the order each number added stands on
     * @param levels     the levels the sum takes
     */
    record OfARemainderAndAForm(LinearForm<NumericTerm> dividend, Map<NumericTerm, Carrier> on,
                                BigInteger divisor, WholeNumberRuns remainders,
                                LinearForm<NumericTerm> added, Map<NumericTerm, Carrier> addedOn,
                                LevelSpace levels, Criterion where) implements Standing {

        public OfARemainderAndAForm {
            on = Map.copyOf(on);
            addedOn = Map.copyOf(addedOn);
            if (dividend.coefs().isEmpty() || !on.keySet().equals(dividend.coefs().keySet())
                    || divisor.signum() <= 0 || remainders == null || added.coefs().isEmpty()
                    || !addedOn.keySet().equals(added.coefs().keySet())
                    || added.coefs().keySet().stream().anyMatch(number -> dividend.coefs()
                            .keySet().stream().anyMatch(number::sharesAPlaceWith))) {
                throw new IllegalArgumentException("a remainder is added to a form over other"
                        + " numbers than its own, each on one order, and divided by a divisor"
                        + " above nought: " + dividend + " by " + divisor + " plus " + added);
            }
        }

        /** Every remainder {@code divisor} leaves. */
        static WholeNumberRuns every(BigInteger divisor) {
            return WholeNumberRuns.one(BigInteger.ZERO, divisor.subtract(BigInteger.ONE));
        }

        /**
         * At the remainders {@code way} leaves this remainder as well: a row composed at another
         * is one the way turns away, so a remainder the item may be at and the way may not is one
         * no row along it is at.
         */
        @Override
        public Standing alongTheWay(Reachability.Reaching way) {
            WholeNumberRuns left = remainders;
            for (OnTheWay.TakenIn cut : way.boundedOnTheWay()) {
                if (cut.demand() instanceof RowDemand.OnARemainder asked
                        && asked.dividend().equals(dividend)
                        && asked.remainder().divisor().equals(divisor)) {
                    left = left.and(asked.leaves());
                }
            }
            return left.equals(remainders) ? this : new OfARemainderAndAForm(dividend, on, divisor,
                    left, added, addedOn, levels, where);
        }
    }

    /**
     * How many elements of a container meet a statement, at a number or in a run of them.
     *
     * <p>What the row has to hold is elements: so many meeting the statement, and the rest
     * whatever the run leaves room for. Not a value at a position — the count is written nowhere,
     * and a search that wrote a number at the container would write a list of the wrong kind.
     *
     * @param count   the count: the container its elements are counted in, and what an element is
     *                counted for meeting
     * @param numbers every number of a row the statement reads, the element's own among them
     */
    record OfACount(CountedElements count, List<NumericTerm> numbers,
                    Criterion where) implements Standing {

        public OfACount {
            numbers = List.copyOf(numbers);
        }
    }

    /**
     * How many elements of a container meet a statement, together with what a form of the input's
     * numbers comes to, at a level of the two added up.
     *
     * <p>Two things a row has to be at: so many elements meeting the statement, and the numbers of
     * the form standing where they add up to what the level leaves. Neither is the item alone, and
     * the count is the composing's to meet where the numbers are placed ({@link CardinalityComposer}).
     *
     * @param count  the count, as {@link OfACount} has it
     * @param form   what is added to the count, with no constant
     * @param on     the order each number of the form stands on
     * @param levels the levels the sum takes
     */
    record OfACountAndAForm(CountedElements count, LinearForm<NumericTerm> form,
                            Map<NumericTerm, Carrier> on, LevelSpace levels,
                            Criterion where) implements Standing {

        public OfACountAndAForm {
            on = Map.copyOf(on);
            if (form.coefs().isEmpty() || !on.keySet().equals(form.coefs().keySet())) {
                throw new IllegalArgumentException("a form is added to the count over the numbers it"
                        + " names, each on one order: " + form + " against " + on.keySet());
            }
        }
    }
}
