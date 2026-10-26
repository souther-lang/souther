package souther.compiler.meaning;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.numeric.UnheldNumber;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A statement read over {@link Quantity.TheKeptTotal}, written for one way its elements are kept:
 * each total replaced by what the way makes of it.
 *
 * <p>The one place a comparison read once for every way of keeping is made into the statement of a
 * way. It takes only statements built of relations over quantities and of the joins of them, where
 * the total is no more than a number in a form; any other part may hold it anywhere, and is no
 * statement to give a way to ({@link #canBeGiven}).
 */
public final class GivenTotals {

    private GivenTotals() {
    }

    /** Whether {@code stated} is made of parts that {@link #in} can give a way. */
    public static boolean canBeGiven(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.InTheStrings _,
                 Proposition.LastToHold _ -> true;
            case Proposition.Compared compared -> compared.relation() instanceof Relation.Affine
                    || compared.relation() instanceof Relation.Ordered;
            case Proposition.All all -> all.parts().stream().allMatch(GivenTotals::canBeGiven);
            case Proposition.Any any -> any.parts().stream().allMatch(GivenTotals::canBeGiven);
            case Proposition.WhereItAnswers where -> canBeGiven(where.answers())
                    && canBeGiven(where.states());
            case Proposition.Some _, Proposition.SomeReachable _, Proposition.OnAnApplication _,
                 Proposition.Carried _, Proposition.SoManyHold _, Proposition.Unread _ -> false;
        };
    }

    /**
     * {@code stated} with each total in it given as {@code totals} says — or why a number in it
     * could not be held. Only for a statement {@link #canBeGiven}.
     */
    public static ExactAnswer<Proposition> in(Proposition stated,
                                              Map<Quantity, LinearForm<Quantity>> totals) {
        return switch (stated) {
            case Proposition.Compared compared -> comparedGiven(compared, totals);
            case Proposition.All all -> switch (given(all.parts(), totals)) {
                case ExactAnswer.Held<List<Proposition>>(var parts) ->
                        ExactAnswer.held(Proposition.all(parts));
                case ExactAnswer.Unheld<List<Proposition>>(var why) -> ExactAnswer.unheld(why);
            };
            case Proposition.Any any -> switch (given(any.parts(), totals)) {
                case ExactAnswer.Held<List<Proposition>>(var parts) ->
                        ExactAnswer.held(Proposition.any(parts));
                case ExactAnswer.Unheld<List<Proposition>>(var why) -> ExactAnswer.unheld(why);
            };
            case Proposition.WhereItAnswers where -> switch (in(where.answers(), totals)) {
                case ExactAnswer.Held<Proposition>(var answers) ->
                        switch (in(where.states(), totals)) {
                            case ExactAnswer.Held<Proposition>(var states) ->
                                    ExactAnswer.held(Proposition.whereItAnswers(answers, states));
                            case ExactAnswer.Unheld<Proposition>(var why) ->
                                    ExactAnswer.unheld(why);
                        };
                case ExactAnswer.Unheld<Proposition>(var why) -> ExactAnswer.unheld(why);
            };
            case Proposition.Always _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.SameValue _, Proposition.InTheStrings _,
                 Proposition.LastToHold _ -> ExactAnswer.held(stated);
            case Proposition.Some _, Proposition.SomeReachable _, Proposition.OnAnApplication _,
                 Proposition.Carried _, Proposition.SoManyHold _, Proposition.Unread _ ->
                    throw new IllegalArgumentException("a total is given to a statement of"
                            + " relations and their joins: " + stated);
        };
    }

    private static ExactAnswer<List<Proposition>> given(List<Proposition> parts,
                                                        Map<Quantity, LinearForm<Quantity>> totals) {
        List<Proposition> out = new ArrayList<>(parts.size());
        for (Proposition part : parts) {
            switch (in(part, totals)) {
                case ExactAnswer.Held<Proposition>(var one) -> out.add(one);
                case ExactAnswer.Unheld<Proposition>(var why) -> {
                    return ExactAnswer.unheld(why);
                }
            }
        }
        return ExactAnswer.held(out);
    }

    private static ExactAnswer<Proposition> comparedGiven(
            Proposition.Compared compared, Map<Quantity, LinearForm<Quantity>> totals) {
        if (!(compared.relation() instanceof Relation.Affine(LinearForm<Quantity> form, Rel rel))
                || form.coefs().keySet().stream().noneMatch(totals::containsKey)) {
            return ExactAnswer.held(compared);
        }
        LinearForm<Quantity> given;
        switch (formGiven(form, totals)) {
            case ExactAnswer.Held<LinearForm<Quantity>>(var held) -> given = held;
            case ExactAnswer.Unheld<LinearForm<Quantity>>(var why) -> {
                return ExactAnswer.unheld(why);
            }
        }
        Rel stated = compared.holds() ? rel : rel.denied();
        if (given.coefs().isEmpty()) {
            return ExactAnswer.held(new Proposition.Always(
                    stated.holds(given.constant().signum())));
        }
        Relation.OneWay<Quantity> oneWay = Relation.OneWay.of(given, stated);
        return ExactAnswer.held(Proposition.compared(
                new Relation.Affine(oneWay.form(), oneWay.proposition()), oneWay.holds()));
    }

    /** {@code form} with each atom that is a total read as the form {@code totals} gives it. */
    private static ExactAnswer<LinearForm<Quantity>> formGiven(
            LinearForm<Quantity> form, Map<Quantity, LinearForm<Quantity>> totals) {
        List<LinearForm<Quantity>> parts = new ArrayList<>();
        Set<UnheldNumber> unheld = new LinkedHashSet<>();
        parts.add(LinearForm.constant(form.constant()));
        form.coefs().forEach((atom, weight) -> {
            LinearForm<Quantity> read = totals.containsKey(atom)
                    ? totals.get(atom) : LinearForm.atom(atom);
            switch (read.times(weight)) {
                case ExactAnswer.Held<LinearForm<Quantity>>(var weighed) -> parts.add(weighed);
                case ExactAnswer.Unheld<LinearForm<Quantity>>(var why) -> unheld.add(why);
            }
        });
        return unheld.isEmpty() ? LinearForm.sum(parts)
                : ExactAnswer.unheld(UnheldNumber.ofAll(unheld));
    }
}
