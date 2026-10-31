package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.function.Predicate;

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

    /** The other end: what a number is the least of, its negation is the greatest of. */
    default Extreme other() {
        return switch (this) {
            case Least _ -> GREATEST;
            case Greatest _ -> LEAST;
        };
    }

    /**
     * The end a choice read in {@code cases} ({@link #casesOf}) keeps of two values, or null where
     * it is no choice between those two that keeps one end.
     *
     * <p>Each case answers one of the two and is reached where they stand in some relations; a case
     * is the lesser where each of those relations puts what it answers below or level with the
     * other, and the greater the other way about. Every case the same, and both values answered by
     * some case, is a choice keeping that end whichever way the two stand.
     *
     * @param isOne   whether an expression, as it is compared ({@link #comparedAs}), is the one
     *                value
     * @param isOther whether one is the other
     */
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
     * {@code if b > a then b else a} and {@code if a >= b then a else b} are one choice. A
     * condition comparing the sign of an order is read as a comparison of a sign is read anywhere
     * ({@link TheSignOfAnOrder#read}), so {@code Decimal.compare(a, b) > 0} chooses by the order of
     * {@code a} and {@code b}.
     *
     * @param at    where {@code e} stands
     * @param sides what the reader answers about where it reads
     * @param <E>   what the reader reads a name in
     */
    static <E> List<Choice.ADefinitionCase> casesOf(Core e, E at,
                                                    TheSignOfAnOrder.Sides<E> sides) {
        Core chosen = Core.withoutStanding(e);
        if (chosen instanceof Core.PreservedCall call) {
            return Choice.casesOf(call);
        }
        if (chosen instanceof Core.If iff
                && Core.withoutStanding(iff.cond()) instanceof Core.Binary cond
                && StatedComparison.of(cond, true) instanceof StatedComparison written) {
            StatedComparison stated = TheSignOfAnOrder.read(written, at, sides)
                    instanceof TheSignOfAnOrder.Read.OfTheArguments<E> ordered
                    && ordered.isTheCondition() ? ordered.arguments() : written;
            return List.of(armOf(iff.then(), stated, true), armOf(iff.els(), stated, false));
        }
        return List.of();
    }

    /**
     * What {@code e}, read in {@code at}, is compared as: past every name and every binding whose
     * body is the value ({@link TheSignOfAnOrder.Sides#standing}), and past the value a newtype
     * wears, which orders as what wears it ({@link Location#isStep}). So a choice is read the same
     * however its values are named: {@code w.value} is compared as {@code w}, and a name given
     * {@code l.discount} as {@code l.discount}.
     *
     * @param <E> what the reader reads a name in
     */
    static <E> ValueStanding.ReadThrough<E> comparedAs(Core e, E at,
                                                      TheSignOfAnOrder.Sides<E> sides) {
        ValueStanding.ReadThrough<E> read = sides.standing(e, at);
        while (true) {
            Core.FieldAccess last = switch (Core.withoutStanding(read.value())) {
                case Core.FieldAccess access -> access;
                case Core.FieldProjection projection -> projection.lastAccess();
                default -> null;
            };
            if (last == null || Location.isStep(last.target().type(), last.field(),
                    sides.newtypes())) {
                return read;
            }
            read = sides.standing(last.target(), read.at());
        }
    }

    /**
     * Every value the cases answer or compare that {@code isOne} does not name, in the order they
     * are met: what a choice between that one and something else takes the something else to be,
     * however many times and ways it is written.
     *
     * <p>A choice keeping one end of two values is one where these are all the one other value
     * ({@link #keptBy}), and whether they are is a question about what they come to, which a
     * reader of what they are made of answers and the names they are written with do not: one
     * helper called twice is two expressions.
     */
    static List<Core> besides(List<Choice.ADefinitionCase> cases, Predicate<Core> isOne) {
        List<Core> others = new ArrayList<>();
        for (Choice.ADefinitionCase each : cases) {
            Core answers = onlyValueOf(each.answers());
            if (answers != null && !isOne.test(answers)) {
                others.add(answers);
            }
            for (Choice.FormsStand stands : each.given()) {
                for (LinearForm<Core> side : List.of(stands.left(), stands.right())) {
                    Core value = onlyValueOf(side);
                    if (value != null && !isOne.test(value)) {
                        others.add(value);
                    }
                }
            }
        }
        return List.copyOf(others);
    }

    /**
     * The ends {@code call}, a choice between its two arguments that keeps one end of them, puts on
     * its answer from those of them that read as constants: the greater is at least each of the
     * two, so at least the greatest constant among them, and the lesser at most the least. No end
     * where it is no such choice, or neither argument reads as a constant.
     *
     * @param constant what an argument reads as, or null where it reads as no constant
     */
    public static NumericDomain.Bounds boundsOf(Core.PreservedCall call,
                                                Function<Core, BigDecimal> constant) {
        if (call.args().size() != 2) {
            return NumericDomain.Bounds.OPEN;
        }
        // The cases answer the argument nodes themselves, which a literal or a call is no
        // other expression for.
        Core one = Core.withoutStanding(call.args().get(0));
        Core other = Core.withoutStanding(call.args().get(1));
        Extreme kept = keptBy(Choice.casesOf(call), e -> Core.withoutStanding(e) == one,
                e -> Core.withoutStanding(e) == other);
        if (kept == null) {
            return NumericDomain.Bounds.OPEN;
        }
        BigDecimal end = null;
        for (Core each : call.args()) {
            BigDecimal at = constant.apply(each);
            if (at != null && (end == null || switch (kept) {
                case Greatest _ -> at.compareTo(end) > 0;
                case Least _ -> at.compareTo(end) < 0;
            })) {
                end = at;
            }
        }
        if (end == null) {
            return NumericDomain.Bounds.OPEN;
        }
        Endpoint stands = Endpoint.inclusive(Count.of(end));
        return switch (kept) {
            case Greatest _ -> new NumericDomain.Bounds(stands, null);
            case Least _ -> new NumericDomain.Bounds(null, stands);
        };
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
