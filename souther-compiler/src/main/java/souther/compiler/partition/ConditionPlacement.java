package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;

import java.util.ArrayList;
import java.util.List;

/**
 * Where one condition of a body stands among the positions a behavior is measured at.
 *
 * <p><b>One answer for every reader that puts a condition to classes.</b> What a body tells apart
 * at a position ({@link BodyDistinction}) and which classes a combination of decisions leaves open
 * ({@link InteractionCells}) are the same reading asked twice; worked out apart, a condition could
 * be about one position to the first and another to the second.
 *
 * <p><b>At one position, or under the cases.</b> A condition about a field of a record is about
 * that field's position. A condition about a name every case of a sum spreads is about a value that
 * stands at one position under each case — {@code r.q.flag} at {@code r.q@A.flag} where the row is
 * an {@code A} — so it is a choice of positions, each with what the row has to be to stand there
 * ({@link WhereANameIsWritten}). That condition is not a condition at the sum's position, which is
 * the longest position the name is under; read there, a fork on the flag would be asked which case
 * of the sum it names.
 *
 * <p>A reader acting on the second answer acts on each case only where the way the condition is on
 * can be that case: what the row is taken to be to stand there is part of the answer and not
 * something to put back afterwards.
 */
sealed interface ConditionPlacement {

    /** About the position {@code axis} measures. */
    record AtAPosition(int axis) implements ConditionPlacement {}

    /**
     * About a name the cases of a sum share, which stands at the position under each case measured
     * here.
     *
     * @param underEach one per case whose position is measured, in the order the model declares
     *                  the cases
     */
    record UnderTheCases(List<UnderACase> underEach) implements ConditionPlacement {

        public UnderTheCases {
            underEach = List.copyOf(underEach);
            if (underEach.isEmpty()) {
                throw new IllegalArgumentException(
                        "a condition placed under the cases is placed under at least one of them");
            }
        }
    }

    /**
     * Where a name stands under one case.
     *
     * @param axis  the position measured there
     * @param at    where the name stands under the case, which is the position {@code axis}
     *              measures or the place a number of it is taken
     * @param taken what the row is taken to be for the name to stand there
     */
    record UnderACase(int axis, TermPath at, Requirements taken) {}

    /** About nothing measured here. */
    record AtNoPosition() implements ConditionPlacement {}

    /**
     * About something the reading could not say where it stands, which may be any position: a fork
     * on nothing a position is, or a name under a case whose reading stopped.
     */
    record Unnamed() implements ConditionPlacement {}

    /** Where {@code condition} stands among {@code axes}. */
    static ConditionPlacement of(souther.compiler.reading.Condition condition,
                                 MeasuredInput.MeasuredAxes axes) {
        TermPath name = switch (condition) {
            case souther.compiler.reading.Condition.Case one -> one.at();
            // A number taken over a run is taken of no one place, so there is no name to follow.
            case souther.compiler.reading.Condition.Side one ->
                    one.at() instanceof NumericTerm.FromOnePosition from ? from.position() : null;
            case souther.compiler.reading.Condition.Arm _ -> null;
        };
        if (condition instanceof souther.compiler.reading.Condition.Arm) {
            return new Unnamed();
        }
        if (name != null) {
            WhereANameIsWritten under = WhereANameIsWritten.of(axes.subject().reach(),
                    name.position(), name.requirements(), _ -> true);
            if (under.moves(name)) {
                return underTheCases(condition, under, axes.axes());
            }
        }
        int at = InteractionCells.positionOf(condition, axes.axes());
        return at < 0 ? new AtNoPosition() : new AtAPosition(at);
    }

    /**
     * {@code condition}, about a name that stands where {@code under} says, placed at each of those
     * positions measured here.
     *
     * <p>Every case or nothing said: a case whose reading stopped holds the name at a position
     * whose rules were never read, so which of the measured positions the condition is about is
     * not known there.
     */
    private static ConditionPlacement underTheCases(souther.compiler.reading.Condition condition,
                                                    WhereANameIsWritten under, List<Axis> axes) {
        if (under.someNotWorkedOut() || under.places().isEmpty()) {
            return new Unnamed();
        }
        List<UnderACase> out = new ArrayList<>();
        for (WhereANameIsWritten.Place place : under.places()) {
            int axis = measuring(condition, place.position(), axes);
            if (axis >= 0) {
                out.add(new UnderACase(axis, place.position(), place.taken()));
            }
        }
        return out.isEmpty() ? new AtNoPosition() : new UnderTheCases(out);
    }

    /**
     * The axis that measures what {@code condition} is about once the name stands at {@code at}, or
     * -1 where none does.
     *
     * <p>The position itself for a case of a value, and the same number of it for a comparison —
     * the value standing there, or what the same operation takes of it with what it was given.
     */
    private static int measuring(souther.compiler.reading.Condition condition, TermPath at,
                                 List<Axis> axes) {
        for (int i = 0; i < axes.size(); i++) {
            NumericTerm.FromOnePosition term = axes.get(i).term();
            if (!term.position().equals(at)) {
                continue;
            }
            boolean same = switch (condition) {
                case souther.compiler.reading.Condition.Case _ ->
                        term instanceof NumericTerm.ValueOf;
                case souther.compiler.reading.Condition.Side one -> sameNumber(term, one.at());
                case souther.compiler.reading.Condition.Arm _ -> false;
            };
            if (same) {
                return i;
            }
        }
        return -1;
    }

    /** Whether {@code measured} is the number {@code asked} is, taken at another position. */
    private static boolean sameNumber(NumericTerm.FromOnePosition measured, NumericTerm asked) {
        return switch (asked) {
            case NumericTerm.ValueOf _ -> measured instanceof NumericTerm.ValueOf;
            case NumericTerm.TakenOf taken -> measured instanceof NumericTerm.TakenOf there
                    && there.operation().equals(taken.operation())
                    && there.arguments().equals(taken.arguments());
            case NumericTerm.TakenOver _ -> false;
        };
    }
}
