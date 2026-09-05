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
        return switch (value) {
            case Value.Text text ->
                    seen instanceof ObservedValue.Text it && it.value().equals(text.value());
            case Value.Truth truth ->
                    seen instanceof ObservedValue.Bool it && it.value() == truth.value();
            // Compared as numbers and not as writings of them. `1.0m` and `1.00m` are one value
            // where they are written, and the reading that named this class already holds them as
            // one (`Value.Number`).
            case Value.Number number -> switch (seen) {
                case ObservedValue.Integer it ->
                        BigDecimal.valueOf(it.value()).compareTo(number.value()) == 0;
                case ObservedValue.Decimal it -> it.value().compareTo(number.value()) == 0;
                default -> false;
            };
            case Value.Case one -> switch (seen) {
                case ObservedValue.Unit it -> one.data().equals(it.type());
                case ObservedValue.Constructed it -> one.data().equals(it.type());
                default -> false;
            };
        };
    }
}
