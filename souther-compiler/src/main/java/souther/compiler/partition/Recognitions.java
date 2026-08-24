package souther.compiler.partition;

import souther.compiler.inputs.Membership;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.observe.ObservedValue;
import souther.compiler.values.Value;

import java.math.BigDecimal;

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

    /** One told apart by looking at the value, which there has to be one of to look at. */
    private static Membership byShape(ObservedValue value,
                                      java.util.function.Predicate<ObservedValue> holds) {
        Membership.Incomplete unread = Membership.unread(value);
        return unread != null ? unread : Membership.of(holds.test(value));
    }

    /**
     * What a class about a count makes of a value: the count is read, and then asked about.
     *
     * <p>The three answers a reading has, in one place. A value that is not a number is a value the
     * class does not hold; a number that could not be read is why nobody can say; and only a number
     * that arrived reaches the question the class is actually about.
     */
    private static Membership counted(Recognition.OfACount count, ObservedValue value) {
        return switch (count.term().read(value, count.carrier())) {
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
