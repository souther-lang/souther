package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

/**
 * Which end of two values a call choosing between them keeps: the lesser or the greater.
 *
 * <p>Read off the cases the operation is defined in ({@link Choice#casesOf}) and from no name the
 * operation has. {@code Int.min(a, b)} is {@code a} where {@code a < b} and {@code b} otherwise, so
 * every case answers the one of the two that is not above the other, and the call keeps the
 * lesser; an operation written the other way round keeps the greater. A call one of whose cases
 * answers the greater and another the lesser keeps neither.
 *
 * <p>Two records and not an enumeration, because a question about a number carries this and what a
 * question carries is built of records under sealed interfaces.
 */
public sealed interface Extreme permits Extreme.Least, Extreme.Greatest {

    /** The lesser of the two, either where they are level. */
    record Least() implements Extreme {}

    /** The greater of the two, either where they are level. */
    record Greatest() implements Extreme {}

    Extreme LEAST = new Least();

    Extreme GREATEST = new Greatest();

    /**
     * The end {@code e} keeps of two values, or null where it is no call choosing between those two
     * that keeps one end.
     *
     * <p>Each case answers one of the two and is reached where they stand in some relations; a case
     * is the lesser where each of those relations puts what it answers below or level with the
     * other, and the greater the other way about. Every case the same, and both values answered by
     * some case, is a call keeping that end whichever way the two stand.
     *
     * @param isOne   whether an expression is the one value
     * @param isOther whether an expression is the other
     */
    static Extreme keptBy(Core e, Predicate<Core> isOne, Predicate<Core> isOther) {
        if (!(Core.withoutStanding(e) instanceof Core.PreservedCall call)) {
            return null;
        }
        List<Choice.ADefinitionCase> cases = Choice.casesOf(call);
        Extreme kept = null;
        boolean answersOne = false;
        boolean answersOther = false;
        for (Choice.ADefinitionCase each : cases) {
            Core answers = onlyValueOf(each.answers());
            boolean one = answers != null && isOne.test(answers);
            boolean other = answers != null && isOther.test(answers);
            if (one == other || each.given().isEmpty()) {
                return null;
            }
            Predicate<Core> answered = one ? isOne : isOther;
            Predicate<Core> beside = one ? isOther : isOne;
            for (Choice.FormsStand stands : each.given()) {
                Extreme here = endOf(stands, answered, beside);
                if (here == null || (kept != null && !kept.equals(here))) {
                    return null;
                }
                kept = here;
            }
            answersOne |= one;
            answersOther |= other;
        }
        return answersOne && answersOther ? kept : null;
    }

    /** The end what {@code answered} names is where {@code stands} puts it against what
     *  {@code beside} names, or null where the relation is between other values or orders neither
     *  way. */
    private static Extreme endOf(Choice.FormsStand stands, Predicate<Core> answered,
                                 Predicate<Core> beside) {
        Core left = onlyValueOf(stands.left());
        Core right = onlyValueOf(stands.right());
        if (left == null || right == null) {
            return null;
        }
        Rel rel;
        if (answered.test(left) && beside.test(right)) {
            rel = stands.rel();
        } else if (beside.test(left) && answered.test(right)) {
            rel = stands.rel().turned();
        } else {
            return null;
        }
        return switch (rel) {
            case LT, LE -> LEAST;
            case GT, GE -> GREATEST;
            case EQ, NE -> null;
        };
    }

    /** The one value {@code form} is, taken once and with nothing added, or null where it is
     *  arithmetic. */
    private static Core onlyValueOf(LinearForm<Core> form) {
        if (form.constant().signum() != 0 || form.coefs().size() != 1) {
            return null;
        }
        Map.Entry<Core, ExactRatio> only = form.coefs().entrySet().iterator().next();
        return only.getValue().compareTo(ExactRatio.ONE) == 0 ? only.getKey() : null;
    }
}
