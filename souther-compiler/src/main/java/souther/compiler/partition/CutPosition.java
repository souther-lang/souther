package souther.compiler.partition;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Towards;
import souther.compiler.numeric.UnheldNumber;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.math.RoundingMode;
import java.util.Optional;
import java.util.OptionalInt;

/**
 * Where a rule's line falls on the quantity it cuts, in that quantity's own units.
 *
 * <p>Held as what the rule wrote and how much of the quantity it wrote it in, rather than as the
 * number that comes of dividing one by the other. {@code 3 * d <= 1} puts its line at a third, and
 * the pair says where that is in the numbers the rule was written with.
 *
 * <p>A report does not write the pair back. Two rules can draw one line in different numbers, and
 * the class they part is named once, so {@link Seam#asARuleAbout} writes the line from where it
 * falls ({@link #asARule}), reduced.
 *
 * <p>The exactness no longer rests on the pair. A level is an exact ratio wherever the quantity
 * counts to one, so dividing here loses nothing; what the pair keeps is the rule's own units, and
 * {@code 3 * d <= 1} and {@code d <= 1 / 3} draw one line and are two ways of writing it.
 *
 * @param written what the rule compared against, on the form it was written in
 * @param per     how much of the quantity that form is, which is never zero and never negative
 */
public record CutPosition(Level written, ExactRatio per) implements Comparable<CutPosition> {

    public CutPosition {
        if (written == null || per == null || per.signum() <= 0) {
            throw new IllegalArgumentException(
                    "a position is a level and a positive share of the quantity: " + written + " / "
                            + per);
        }
    }

    /**
     * Whether a line written at {@code written} over {@code per} of the quantity falls at a number an
     * exact ratio holds.
     *
     * <p>Asked before a position is built, because every reading of one takes the number it falls at
     * ({@link #exactly}) and a position whose number has no representation has nothing to answer
     * with. An order with no numbers is never divided, so it is always held.
     */
    static boolean holdsWhereItFalls(Level written, ExactRatio per) {
        return placed(written, per).isHeld();
    }

    /**
     * The position a line written at {@code written} over {@code per} of the quantity is, or the way
     * the number it falls at was not held.
     *
     * <p>The one way to build a position from a number this compiler worked out: a position whose
     * number has no representation has nothing to answer with, so it is not built.
     */
    static ExactAnswer<CutPosition> placed(Level written, ExactRatio per) {
        ExactRatio at = numberOf(written);
        CutPosition line = new CutPosition(written, per);
        return at == null ? ExactAnswer.held(line)
                : at.dividedBy(per).flatMap(_ -> ExactAnswer.held(line));
    }

    /** A line at a level of the quantity itself, which is what a rule that wrote the whole of it
     *  draws. */
    public static CutPosition at(Level written) {
        return new CutPosition(written, ExactRatio.ONE);
    }

    /**
     * Where this line falls, as the exact number it is — or null on an order with no numbers.
     *
     * <p>What the rule wrote over how much of the quantity it wrote, which is exact: both are
     * ratios and a ratio divided by a ratio is one. A third comes back a third, and the reader that
     * needs it as a value of something asks {@link #asAValueOf}.
     */
    public ExactRatio exactly() {
        ExactRatio at = numberOf(written);
        // A line a rule wrote over the whole quantity is where it was written, and dividing by one
        // would only put the same ratio back into lowest terms. Nearly every line is one of these,
        // and every comparison of two lines asks both for this.
        if (per.equals(ExactRatio.ONE)) {
            return at;
        }
        return at == null ? null
                : at.dividedBy(per).orFail("a position built where its number has no representation");
    }

    /**
     * What makes two positions one position: where the line falls, and not the units it was said in.
     *
     * <p>A third and two sixths are one place, which an exact ratio in lowest terms already says —
     * so the ratio names itself here, by its own canonical parts and not by its digits. A line on a
     * quantity written at a millionth is one this tells from every other; that is what a name is
     * for, and spelling the millionth out is not part of it.
     *
     * <p>An order with no numbers answers with its own value. Nothing scales such a quantity — a
     * rule holding two strings apart writes the whole of it — so there is no fraction to reduce.
     */
    public String key() {
        ExactRatio at = exactly();
        if (at == null) {
            return written.key();
        }
        return at.key();
    }

    /**
     * This line's coordinate written out as text.
     *
     * <p>A rule that wrote the whole of the quantity drew its line at one of the quantity's own
     * levels, which is spelled as a level is ({@link Level#spelled}). A rule that wrote a multiple
     * drew it where the quantity stands at no level of its own, so what is left to write is the
     * number ({@link ExactRatio#spelled}).
     *
     * <p>Apart from {@link #key()}, which tells two lines apart and writes neither: a line on a
     * quantity written at a millionth has a name of a few characters and takes a million to write.
     */
    public String spelled() {
        ExactRatio at = exactly();
        if (at == null) {
            return written.spelled();
        }
        Level itself = asALevelOfTheQuantity();
        return itself == null ? at.spelled() : itself.spelled();
    }

    /**
     * This line in the one representation {@link #key()} names: the line in its terms
     * ({@link #asARule}).
     *
     * <p>So that a value holding a position and compared as a value answers what {@link #key()}
     * would. A third and two sixths come back the same, and so do a line at {@code 0} and one at
     * {@code 0.00}. The terms answer for every line a ratio holds, so this does too.
     *
     * <p>A function of the line's meaning and of nothing the host can hold: the place is the number
     * the terms come to, whichever order the rule was written on and however many digits that
     * number has. Which carrier a rule was written on is the quantity's and is no part of where a
     * line falls, and two lines compared by this are on one quantity. A representation that depended
     * on whether the host could write the count would make the identity of one line change with the
     * host.
     *
     * <p>An order with no numbers has no fraction to reduce, and its place is its own value.
     */
    public CutPosition canonical() {
        ExactRatio.Terms rule = asARule();
        if (rule == null) {
            return new CutPosition(written.canonical(), per);
        }
        return new CutPosition(new Level.OfTheQuantity(rule.comesTo()), rule.per());
    }

    /**
     * The same line on the quantity read the other way round.
     *
     * <p>The place negates and the share does not. How much of the quantity the rule wrote is a
     * fact about the rule's form and says nothing about which way the quantity is measured, so a
     * line at a third of {@code a - b} is at minus a third of {@code b - a} and is still a third of
     * whatever was written.
     */
    public CutPosition reflected() {
        return new CutPosition(written.negated(), per);
    }

    /**
     * This line as a value of the quantity, or null where it is not one.
     *
     * <p>The one way to get a level out of a position, and it answers null exactly where the rule
     * wrote a multiple of the quantity and the line does not land on one of its values — a third is
     * where {@code 3 * d <= 1} cuts and is no decimal this language writes. Every reader that took
     * the level the rule was written with for a value of the quantity had it wrong by the multiple:
     * a run read its own end against it, a line was asked whether it keeps a value it is not at, and
     * a search was handed a level of one order to look for on another.
     */
    public Level asALevelOfTheQuantity() {
        return per.equals(ExactRatio.ONE) ? written : null;
    }

    /**
     * A level of the quantity, said on the order the rule wrote this line on.
     *
     * <p>What {@link #written} is on, and so what the number the rule wrote and the range of the
     * form it wrote are on. A seam names the values either side of the line in the quantity's own
     * units, which is what a value of the position is written in; held beside the threshold or
     * beside where the written form runs, such a value is on another order by a factor of
     * {@link #per}. {@code 2 * a < 6000} leaves off at {@code a = 2999}, which the form calls 5998.
     *
     * @return the level, or the way the number it comes to was not held
     */
    public ExactAnswer<Level> asWritten(Level ofTheQuantity) {
        ExactRatio number = ofTheQuantity.asANumber();
        if (number == null || per.equals(ExactRatio.ONE)) {
            return ExactAnswer.held(ofTheQuantity);
        }
        return number.times(per).map(Level.OfTheQuantity::new);
    }

    /**
     * The same line, said in units {@code k} times smaller.
     *
     * <p>A line at a place is at {@code k} times that number where the unit is a {@code k}th of the
     * one it was said in: what a quantity's own level is, the form that wrote {@code k} of it calls
     * {@code k} times as much.
     *
     * @return the position, or the way the number it comes to was not held
     */
    public ExactAnswer<CutPosition> times(ExactRatio k) {
        ExactRatio at = numberOf(written);
        if (at == null || k.equals(ExactRatio.ONE)) {
            return ExactAnswer.held(this);
        }
        // Scaled by exactly the share the rule wrote, the share divides out: the line is at the
        // number the rule carried, in the units the rule carried it in. Left in, the position was
        // right and the reading of it was not — a line the form does stand at went on answering
        // that the quantity has no value there, and the run above it could not say where it starts.
        if (k.equals(per)) {
            return ExactAnswer.held(new CutPosition(new Level.OfTheQuantity(at), ExactRatio.ONE));
        }
        return at.times(k).flatMap(scaled -> placed(new Level.OfTheQuantity(scaled), per));
    }

    /**
     * This line as a value of the position the quantity is a multiple of, empty where the position
     * holds none there, and unheld where the host had no room to write the count out.
     *
     * <p>Apart from {@link #asALevelOfTheQuantity}, which asks about the order the rule wrote the
     * line on. This asks about the position underneath it, and the two differ exactly where a rule
     * wrote a multiple: {@code 2 * n == 8} names four and {@code 2 * n == 9} names nothing, and both
     * are lines of an order whose values are the even numbers.
     *
     * <p>The carrier edge for a line: an exact place becomes a value here or is none
     * ({@link Count#written}). A third is no count at all, and a count the carrier's own values step
     * past is no value of it either.
     */
    public ExactAnswer<Optional<Place>> asAValueOf(souther.compiler.check.Carrier carrier) {
        if (carrier == null) {
            return ExactAnswer.held(Optional.empty());
        }
        ExactRatio at = exactly();
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so its line is its own value and there is nothing to divide.
        if (at == null) {
            return ExactAnswer.held(per.equals(ExactRatio.ONE)
                    ? Optional.of(written.asAPlace()) : Optional.empty());
        }
        return Count.written(at).flatMap(count -> ExactAnswer.held(
                count.map(carrier::onTheGrid)));
    }

    /**
     * Whether a value of the quantity is below, at or above where this line falls.
     *
     * <p>Both are exact, so the comparison is exact and a line at a place no value stands at is
     * compared without being written down: a fifth is under a third and a half is over it.
     */
    public int compare(Level value) {
        ExactRatio line = exactly();
        ExactRatio of = numberOf(value);
        // An order with no numbers is never scaled — a rule holding two strings apart writes the
        // whole of what it cuts — so the two are places of one order and compare as they stand.
        if (line == null || of == null) {
            return value.asAPlace().compareTo(written.asAPlace());
        }
        return of.compareTo(line);
    }

    /**
     * Whether this line falls below, at or above where {@code other} does.
     *
     * <p>Exact, for the reason the rest of this is: a line at a third and one at two sixths fall in
     * one place, and neither of them is a number this language can write out to compare.
     */
    @Override
    public int compareTo(CutPosition other) {
        ExactRatio mine = exactly();
        ExactRatio theirs = other.exactly();
        if (mine == null || theirs == null) {
            return written.asAPlace().compareTo(other.written.asAPlace());
        }
        return mine.compareTo(theirs);
    }

    /**
     * This line as a rule an author could have written it: how much of the quantity, and what it
     * comes to.
     *
     * <p>Reduced, so that the two rules that draw one line write it one way — a third and two
     * sixths both come back as {@code 3} and {@code 1}. What names a class where the position holds
     * no value at the line: {@code 3 * d <= 1} says exactly where the values part and says it in
     * numbers this language has, which dividing them out would not.
     *
     * <p>The one decomposition of a line into a rule. The name a report gives the line, the multiple
     * two ends of a run share and the position the line is compared as are all read off it, so what
     * one of them can write the others can compare ({@link ExactRatio#asTerms}).
     *
     * @return the line's terms, or null on an order with no numbers
     */
    public ExactRatio.Terms asARule() {
        ExactRatio at = exactly();
        return at == null ? null : at.asTerms();
    }

    /**
     * The same, asked of a number the quantity comes to.
     *
     * <p>For a reader holding what a form added up to at one row rather than a level of an order:
     * the two are the same number and only one of them is a value of anything.
     */
    public int compare(ExactRatio value) {
        ExactRatio line = exactly();
        if (line == null) {
            throw new IllegalStateException(
                    "an order with no numbers was compared against one: " + written);
        }
        return value.compareTo(line);
    }

    /** The same, asked of a place of the order this line falls on. */
    public int compare(souther.compiler.numeric.Place at) {
        ExactRatio line = exactly();
        // The same two answers as above, and the second for the same reason: an order with no
        // numbers is never scaled, so its places compare as they stand — and two carriers' places
        // brought together say so themselves rather than arriving here as a null.
        return at instanceof Count count && line != null
                ? count.exactly().compareTo(line)
                : at.compareTo(written.asAPlace());
    }

    /**
     * What {@link #justBeyond} comes to: a whole number of the quantity's units to start looking
     * from, an order with no numbers to start from at all, or which way the exact arithmetic could
     * not round the line inward.
     *
     * <p>The second and the third told apart, where a collapsed {@code null} once ran them
     * together: an order with no numbers never needed the rounding in the first place, and a
     * caller reading both as one absence was reading "this compiler could not work out where to
     * look" as "there is nowhere to look" — sound for the {@code witness} the space
     * {@link LevelSpace#onACarrier} returns, which only ever needs a candidate and answers
     * {@code Witness.NONE} either way, and not sound for that same space's {@code inspect}, whose
     * bound this feeds directly into and which an absent end there widens to the carrier's own
     * extent.
     */
    public sealed interface JustBeyond {

        /** A place to start looking from. */
        record At(Place place) implements JustBeyond {
            public At {
                if (place == null) {
                    throw new IllegalArgumentException("a place to start looking from is a place");
                }
            }
        }

        /** An order with no numbers, which is never scaled and so never needed the rounding. */
        record NoNumericPlace() implements JustBeyond {}

        /** A model's own decimals put the line far enough from an ordinary one in scale that the
         *  exact arithmetic could not round it to this many digits. */
        record NotWorkedOut(UnheldNumber why) implements JustBeyond {
            public NotWorkedOut {
                if (why == null) {
                    throw new IllegalArgumentException("a refusal says why");
                }
            }
        }
    }

    /**
     * A whole number of the quantity's units on one side of this line, for a search to start from.
     *
     * <p>Where the line falls between two of them, the whole number that way is past it — a third
     * rounded up is one and rounded down is nothing, and both are on the side they were rounded to.
     * A bound and never the answer: what is at a run is the run's to say, and this is only where to
     * begin looking.
     */
    public JustBeyond justBeyond(Towards towards, int digits) {
        ExactRatio line = exactly();
        if (line == null) {
            return new JustBeyond.NoNumericPlace();
        }
        RoundingMode away = towards == Towards.ABOVE ? RoundingMode.CEILING : RoundingMode.FLOOR;
        BigDecimal rounded;
        switch (line.asDecimal(away, digits)) {
            case ExactAnswer.Held<BigDecimal> held -> rounded = held.value();
            case ExactAnswer.Unheld<BigDecimal> unheld -> {
                return new JustBeyond.NotWorkedOut(unheld.why());
            }
        }
        // Strictly past, which rounding gives only where the line is not itself a number of that
        // many digits. A line the quantity does stand at rounds to itself, and the run beyond it
        // does not hold it.
        if (ExactRatio.of(rounded).compareTo(line) != 0) {
            return new JustBeyond.At(new Count(rounded));
        }
        // One of the last of those places further on, added as numbers: the sum of the line and
        // one step can be a number with more digits than the host holds, which is said rather than
        // let a decimal sum throw over it.
        ExactRatio step = ExactRatio.of(new BigDecimal(BigInteger.ONE, digits));
        ExactAnswer<BigDecimal> past = switch (towards == Towards.ABOVE
                ? line.plus(step) : line.minus(step)) {
            case ExactAnswer.Held<ExactRatio> beyond -> beyond.value().asDecimal(away, digits);
            case ExactAnswer.Unheld<ExactRatio> unheld -> ExactAnswer.unheld(unheld.why());
        };
        return switch (past) {
            case ExactAnswer.Held<BigDecimal> at -> new JustBeyond.At(new Count(at.value()));
            case ExactAnswer.Unheld<BigDecimal> unheld -> new JustBeyond.NotWorkedOut(unheld.why());
        };
    }

    /**
     * How many digits it takes to name a number between this line and {@code other}.
     *
     * <p>Worked out from the two places and not guessed. Two lines are a definite distance apart —
     * a third and a third and a hundred-billionth are — and a decimal lies between any two of them;
     * how many digits it needs is what that distance says. Tried at a fixed handful of scales
     * instead, a run narrower than the widest of them was reported as one no value of the position
     * lies inside, which is a false answer rather than a search that gave up.
     *
     * <p>Exact, because both lines are: the digits needed are what it takes for a tenth of that many
     * to fit inside the distance. Zero where the two are the same place, which no run has.
     *
     * <p>Read off the distance's size rather than by forming one over it and counting the digits of
     * what came back. A distance of a millionth has an answer of about a million, and the number
     * built to be measured had as many digits as the answer counts.
     *
     * @return the count, or which way this host cannot name it — the two lines a model's own
     *         decimals put far enough apart in scale that their difference has no representation
     *         this host writes ({@link UnheldNumber#NO_REPRESENTATION_EXISTS}, the exact
     *         arithmetic's own answer), or the count itself past what an {@code int} names, which
     *         is the same word for the same reason: no wider run holds an {@code int} that counts
     *         higher, so nothing here is short of room either way
     */
    public ExactAnswer<Integer> digitsToTellApartFrom(CutPosition other) {
        ExactRatio mine = exactly();
        ExactRatio theirs = other.exactly();
        if (mine == null || theirs == null) {
            return ExactAnswer.held(0);
        }
        return switch (mine.minus(theirs)) {
            case ExactAnswer.Held<ExactRatio> held -> {
                ExactRatio apart = held.value().abs();
                if (apart.isZero()) {
                    yield ExactAnswer.held(0);
                }
                OptionalInt places = apart.placesItStandsAbove();
                // `+ 1` overflows exactly where `places` is already the top of what an `int`
                // counts, so that one value is folded in with the search finding none at all:
                // both leave this with a count no `int` here names.
                yield places.isPresent() && places.getAsInt() < Integer.MAX_VALUE
                        ? ExactAnswer.held(places.getAsInt() + 1)
                        : ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS);
            }
            case ExactAnswer.Unheld<ExactRatio> unheld -> ExactAnswer.unheld(unheld.why());
        };
    }

    private static ExactRatio numberOf(Level level) {
        return level.asANumber();
    }
}
