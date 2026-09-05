package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.values.Value;

import java.math.BigDecimal;
import java.util.Objects;

/**
 * Reading one {@link Recognition} against one value.
 *
 * <p>The capability beside the value, and the only thing that executes a class's meaning. A reader
 * that wants to place a row asks here; nothing else in this compiler works out from the
 * declarations what a class recognises, which is what kept the same meaning derived in more than one
 * place while a class was a function somebody had built.
 *
 * <p>Exhaustive over {@link Recognition} with no {@code default}, so a distinction added to the
 * language stops this compiling rather than arriving as a class that quietly recognises nothing.
 */
public final class Recognitions {

    private Recognitions() {}

    /** This class, as something to ask of a row. */
    public static Classifier reading(Recognition what) {
        return value -> membershipOf(what, value);
    }

    /**
     * What {@code what} makes of {@code value}.
     *
     * <p>Which arms answer for an observation that did not arrive, and which read it themselves, is
     * the difference between the two kinds of class and not an oversight. A class told apart by the
     * shape of the value is asked of the value, so there being none is settled before it is asked —
     * that is a fact about the observation rather than a thing the class declines. A class about a
     * count reads through the value to a number, and what stopped the reading is what it has to
     * say, so it is handed the observation as it stands ({@link Membership}).
     */
    public static Membership membershipOf(Recognition what, ObservedValue value) {
        // A class is put to a value that stands, and whether one stands there was settled by
        // whatever walked to the position. Answered here instead, this entry would say one thing
        // for a class that looks at a shape and another for a class that reads a number — one
        // question with two answers, decided by which kind of class a caller happened to hold.
        Objects.requireNonNull(value, "a class is put to a value that stands at the position");
        return switch (what) {
            case Recognition.Under under ->
                    membershipOf(under.inner(), Classifier.inside(under.worn(), value));
            case Recognition.Truth truth -> byShape(value, seen ->
                    seen instanceof ObservedValue.Bool it && it.value() == truth.value());
            case Recognition.Held held -> byShape(value, seen ->
                    held.present() != (seen instanceof ObservedValue.Absent));
            case Recognition.OfCase one -> byShape(value, seen -> switch (seen) {
                case ObservedValue.Unit it -> one.leaf().equals(it.type());
                case ObservedValue.Constructed it -> one.leaf().equals(it.type());
                default -> false;
            });
            case Recognition.AtAValue one -> byShape(value, seen -> holds(seen, one.value()));
            case Recognition.OfACount count -> counted(count, value);
            // Asked of the set, which is where the shapes a set comes in are told apart. Walked
            // here instead, this would be a second place they are enumerated, and the day a third
            // shape arrived is exactly where it would not be.
            case Recognition.OfASet set -> byShape(value, seen -> {
                Value written = writtenValueOf(seen);
                return written != null && set.values().has(written);
            });
            case Recognition.Nothing _ -> Membership.NO_MATCH;
        };
    }

    /** One told apart by looking at the value, which there is one of to look at. */
    private static Membership byShape(ObservedValue value,
                                      java.util.function.Predicate<ObservedValue> holds) {
        Membership.Incomplete unread = Membership.unread(value);
        return unread != null ? unread : Membership.of(holds.test(value));
    }

    /**
     * Whether {@code what} holds the number at {@code place}.
     *
     * <p>The other way a class is asked, and the one for a reader that has a number rather than a
     * row. A line is a place on the order of the number the rules cut, and finding which class it
     * falls in is what says which side of it a condition admits — asked with a value instead, the
     * question is about what stands at the position, which for a number taken of it is a different
     * thing entirely and never the one that was drawn.
     *
     * <p>No carrier and no term. Which order the place is on is settled by the axis it came from:
     * the classes of an axis are classes of the number it measures ({@link Axis}), so a place on
     * that number's order and the class are already about one thing, and a reader that named either
     * of them here could name a different one.
     *
     * <p>Exhaustive over {@link Recognition} with no {@code default}. A class about what stands at
     * the position answers from where that value sits, which is written down when the class is made;
     * one about nothing that is placed anywhere holds no place.
     */
    public static boolean holdsTheNumberAt(Recognition what, Place place) {
        return switch (what) {
            case Recognition.OfACount count -> holds(count.is(), place, count.carrier());
            // The names a value is written under are how a row spells it, and a place wears none.
            case Recognition.Under under -> holdsTheNumberAt(under.inner(), place);
            case Recognition.AtAValue one -> one.at() != null && one.at().sameAs(place);
            case Recognition.Truth ignored -> false;
            case Recognition.Held ignored -> false;
            // A set of the position's values is no run of them, so nothing here is either side of
            // a line. An axis carrying lines refuses such a class before this is ever asked
            // ({@link Recognition#answersAboutAPlace}).
            case Recognition.OfASet ignored -> false;
            // A case of an ordered enumeration sits at a place on that order, written down when the
            // class was built; a case of a sum with no order sits nowhere and is asked nothing.
            case Recognition.OfCase one -> one.at() != null && one.at().sameAs(place);
            case Recognition.Nothing ignored -> false;
        };
    }

    /**
     * What a class about a count makes of a value: the count is read, and then asked about.
     *
     * <p>The three answers a reading has, in one place. A value that is not a number is a value the
     * class does not hold; a number that could not be read is why nobody can say; and only a number
     * that arrived reaches the question the class is actually about.
     *
     * <p>Asked of a value, so there is no fourth. Whether there is a value here was settled by
     * whatever walked to the position, and a class is put to the ones that stand.
     */
    private static Membership counted(Recognition.OfACount count, ObservedValue value) {
        // Read on the order the value is written on; asked on the order the count is compared
        // on. One carrier for both was right while the two could not differ (#1027).
        return switch (count.orders().read(value)) {
            case NumericTerm.Reading.Number number -> Membership.of(
                    holds(count.is(), number.value(), count.carrier()));
            case NumericTerm.Reading.Missing missing -> new Membership.Incomplete(missing.code());
            case NumericTerm.Reading.NotNumber _ -> Membership.NO_MATCH;
        };
    }

    private static boolean holds(Recognition.CountIs is, souther.compiler.numeric.Place at,
                                 souther.compiler.check.Carrier carrier) {
        return switch (is) {
            case Recognition.CountIs.At one -> at.sameAs(one.value());
            case Recognition.CountIs.AwayFrom others ->
                    others.values().stream().noneMatch(at::sameAs);
            case Recognition.CountIs.InARun run ->
                    run.run().holds(new Level.OnACarrier(carrier, at));
        };
    }

    /**
     * Whether an observed value is the one a class is of.
     *
     * <p>Bare, without the names the position wears: {@link Recognition.Under} takes off the ones
     * that are there and asks about the rest, so a value handed over as it stands is answered the
     * same way a row is.
     */
    private static boolean holds(ObservedValue seen, Value value) {
        return value.equals(writtenValueOf(seen));
    }

    /**
     * The value a model would have written for what was observed, or null where nothing writes one.
     *
     * <p>The one crossing between what a run left and what a rule names, and the reason it is one:
     * a class is told from a value here and a class is told from a set of values beside it, and the
     * two asked separately are two answers to which observations count as which written value. So
     * both go through this, and the set is then asked the way any reader asks a set.
     *
     * <p>Null is "no value is written for this" and not "it is unlike everything". A moment, a
     * sequence and a mapping are observations of positions whose values are told apart another way
     * — a moment by the count that stands for it, the others by what they hold — and none of them
     * is a value a rule names ({@link Value}). A value nothing writes is in no set a rule stated,
     * which is what a class of such a set says about it.
     *
     * <p>A constructed value comes back as the case it is. What tells one case from another is
     * which declaration it is, so what it carries is no part of the value here — and a class of a
     * case is a class of every row that built one.
     */
    private static Value writtenValueOf(ObservedValue seen) {
        return switch (seen) {
            case ObservedValue.Text it -> Value.text(it.value());
            case ObservedValue.Bool it -> Value.truth(it.value());
            // Held as the number and not as the writing of it. `1.0m` and `1.00m` are one value
            // where they are written, and `Value.Number` is what holds them as one — so an
            // observation that reads as either comes back as that one value.
            case ObservedValue.Integer it -> Value.number(BigDecimal.valueOf(it.value()));
            case ObservedValue.Decimal it -> Value.number(it.value());
            case ObservedValue.Unit it -> Value.of(it.type());
            case ObservedValue.Constructed it -> Value.of(it.type());
            default -> null;
        };
    }
}
