package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;

/**
 * Which end of two values a choice between them keeps: the lesser or the greater.
 *
 * <p>Read off the cases the choice is made in and from no name an operation has: those an operation
 * is defined in ({@link Choice#casesOf}), or the arms of an {@code if}. {@code Int.min(a, b)} is
 * {@code a} where {@code a < b} and {@code b} otherwise, so every case answers the one of the two
 * that is not above the other, and the call keeps the lesser; an operation written the other way
 * round keeps the greater. A choice one of whose cases answers the greater and another the lesser
 * keeps neither.
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
     * The end {@code e} keeps of two values, or null where it is no choice between those two that
     * keeps one end.
     *
     * <p>Each case answers one of the two and is reached where they stand in some relations; a case
     * is the lesser where each of those relations puts what it answers below or level with the
     * other, and the greater the other way about. Every case the same, and both values answered by
     * some case, is a choice keeping that end whichever way the two stand.
     *
     * @param isOne   whether an expression is the one value
     * @param isOther whether an expression is the other
     */
    static Extreme keptBy(Core e, Predicate<Core> isOne, Predicate<Core> isOther) {
        return keptBy(casesOf(e, UnaryOperator.identity()), isOne, isOther);
    }

    /** The same, of the cases a choice was read in ({@link #casesOf}). */
    static Extreme keptBy(List<Choice.ADefinitionCase> cases, Predicate<Core> isOne,
                          Predicate<Core> isOther) {
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

    /**
     * The cases {@code e} is chosen in, each answering a value and reached where values stand in
     * relations — or none where it is no choice of the two kinds read here.
     *
     * <p>Those of a call the library defines by them ({@link Choice#casesOf}), or the two arms of
     * an {@code if} whose condition is one comparison: the arm taken where it holds is reached
     * under the relation it states, and the other under its denial. {@code Int.max(a, b)},
     * {@code if b > a then b else a} and {@code if a >= b then a else b} are one choice.
     *
     * @param ofTheArguments the comparison a condition states, as the comparison of the values it
     *                       holds exactly where: the condition itself, or — for a reader that can
     *                       read a number where the condition stands — the comparison of the
     *                       arguments of an order whose sign it compares ({@link TheSignOfAnOrder})
     */
    static List<Choice.ADefinitionCase> casesOf(Core e,
                                                UnaryOperator<StatedComparison> ofTheArguments) {
        Core chosen = Core.withoutStanding(e);
        if (chosen instanceof Core.PreservedCall call) {
            return Choice.casesOf(call);
        }
        if (chosen instanceof Core.If iff
                && Core.withoutStanding(iff.cond()) instanceof Core.Binary cond
                && StatedComparison.of(cond, true) instanceof StatedComparison written) {
            StatedComparison stated = ofTheArguments.apply(written);
            return List.of(armOf(iff.then(), stated, true), armOf(iff.els(), stated, false));
        }
        return List.of();
    }

    /** The one value {@code each} answers, or null where it answers arithmetic. */
    static Core answeredBy(Choice.ADefinitionCase each) {
        return onlyValueOf(each.answers());
    }

    /** The arm answering {@code answers}, reached where {@code condition} comes out
     *  {@code holding}. */
    private static Choice.ADefinitionCase armOf(Core answers, StatedComparison condition,
                                                boolean holding) {
        return new Choice.ADefinitionCase(LinearForm.atom(answers), List.of(new Choice.FormsStand(
                LinearForm.atom(condition.left()), condition.relationUnder(holding),
                LinearForm.atom(condition.right()))));
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
