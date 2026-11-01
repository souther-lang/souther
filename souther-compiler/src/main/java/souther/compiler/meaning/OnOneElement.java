package souther.compiler.meaning;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * A statement over the element of a list of every whole number between two, read on one element.
 *
 * <p>The element is a value read off a binding, which no row holds, and the list is from one form
 * of the input's numbers to another ({@link Quantity.AWholeNumberInTurn}). Put at one of its
 * values, the statement is one of the input's numbers alone, and a row is asked it as it is asked
 * any such statement. Which value is the element's is said of the statement too: that it comes
 * round to a value some whole number of turns from the list's start, where the list holds it.
 *
 * <p>The element is put only where this reads through: a relation's form, the dividend of a
 * remainder in it, and what some element of a container meets, inside statements held together.
 * A part weighing it anywhere else keeps it, and a row is not asked that part.
 */
public final class OnOneElement {

    private OnOneElement() {
    }

    /**
     * The element of a list of every whole number between two {@code stated} weighs, where it
     * weighs one and no other value read off a binding of such a list.
     */
    public static Optional<Quantity.OfABinding> theElementOf(Proposition stated) {
        Set<Quantity.OfABinding> found = new LinkedHashSet<>();
        elementsIn(stated, found, Collections.newSetFromMap(new IdentityHashMap<>()));
        return found.size() == 1 ? Optional.of(found.iterator().next()) : Optional.empty();
    }

    /** The elements {@code stated} weighs, put in {@code into}; a part met before, as a
     *  statement shares its parts, is walked once ({@code walked}). */
    private static void elementsIn(Proposition stated, Set<Quantity.OfABinding> into,
                                   Set<Proposition> walked) {
        if (!walked.add(stated)) {
            return;
        }
        switch (stated) {
            case Proposition.All(var parts, var _) ->
                    parts.forEach(each -> elementsIn(each, into, walked));
            case Proposition.Any(var parts, var _) ->
                    parts.forEach(each -> elementsIn(each, into, walked));
            case Proposition.WhereItAnswers(var answers, var states, var _) -> {
                elementsIn(answers, into, walked);
                elementsIn(states, into, walked);
            }
            case Proposition.Some(var _, var ofTheElement, var _, var _) ->
                    elementsIn(ofTheElement, into, walked);
            case Proposition.Compared(Relation.Affine affine, var _, var _) ->
                    elementsIn(affine.form(), into);
            default -> { }
        }
    }

    private static void elementsIn(LinearForm<Quantity> form, Set<Quantity.OfABinding> into) {
        for (Quantity each : form.coefs().keySet()) {
            if (each instanceof Quantity.RemainderOfADividend remainder) {
                elementsIn(remainder.dividend(), into);
            } else if (each instanceof Quantity.OfABinding bound
                    && bound.handed().orElse(null) instanceof Quantity.AWholeNumberInTurn) {
                into.add(bound);
            }
        }
    }

    /**
     * {@code stated} with {@code element} at {@code there}, every relation in it left with no
     * number to weigh the value it comes to — or null where the exact arithmetic cannot hold the
     * element there.
     */
    public static Proposition at(Proposition stated, Quantity.OfABinding element,
                                 LinearForm<Quantity> there) {
        return new Putting(element, there, true, new IdentityHashMap<>()).at(stated);
    }

    /**
     * {@code stated} with {@code element} at {@code there} inside every remainder it weighs it in,
     * and nowhere else: what a remainder leaves at an element it leaves at every element that
     * comes round to it ({@link TheElementComesRound#inItsRemainders}), and the rest is read at
     * the element itself. Null where the exact arithmetic cannot hold the element there.
     */
    public static Proposition inItsRemainders(Proposition stated, Quantity.OfABinding element,
                                              LinearForm<Quantity> there) {
        return new Putting(element, there, false, new IdentityHashMap<>()).at(stated);
    }

    /**
     * One putting of {@code element} at {@code there}, in remainders and, where {@code itself},
     * wherever it is weighed itself.
     *
     * @param put what each part met so far came to, or {@link #CANNOT} where the exact arithmetic
     *            could not hold the element there: a part a statement holds in several places is
     *            put once, and a part that does not weigh the element is itself
     */
    private record Putting(Quantity.OfABinding element, LinearForm<Quantity> there,
                           boolean itself, Map<Proposition, Proposition> put) {

        Proposition at(Proposition stated) {
            Proposition had = put.get(stated);
            if (had == null) {
                Proposition made = atOnce(stated);
                had = made == null ? CANNOT : made;
                put.put(stated, had);
            }
            return had == CANNOT ? null : had;
        }

        private Proposition atOnce(Proposition stated) {
            return switch (stated) {
                case Proposition.Always _ -> stated;
                case Proposition.All(var parts, var _) -> {
                    List<Proposition> each = at(parts);
                    yield each == null ? null : each == parts ? stated : Proposition.all(each);
                }
                case Proposition.Any(var parts, var _) -> {
                    List<Proposition> each = at(parts);
                    yield each == null ? null : each == parts ? stated : Proposition.any(each);
                }
                case Proposition.WhereItAnswers(var answers, var states, var _) -> {
                    Proposition answering = at(answers);
                    Proposition stating = at(states);
                    yield answering == null || stating == null ? null
                            : answering == answers && stating == states ? stated
                            : Proposition.whereItAnswers(answering, stating);
                }
                case Proposition.Some(var container, var ofTheElement, var holds, var _) -> {
                    Proposition met = at(ofTheElement);
                    yield met == null ? null : met == ofTheElement ? stated
                            : new Proposition.Some(container, met, holds);
                }
                case Proposition.Compared(Relation.Affine affine, boolean holds, var _) -> {
                    LinearForm<Quantity> on = formAt(affine.form(), element, there, itself);
                    if (on == null) {
                        yield null;
                    }
                    if (on.equals(affine.form())) {
                        yield stated;
                    }
                    if (on.coefs().isEmpty()) {
                        yield new Proposition.Always(
                                holds == affine.proposition().holds(on.constant().signum()));
                    }
                    Relation.OneWay<Quantity> one = Relation.OneWay.of(on, affine.proposition());
                    yield new Proposition.Compared(new Relation.Affine(one.form(),
                            one.proposition()), holds == one.holds());
                }
                default -> stated;
            };
        }

        /** Each of {@code parts} put, the same parts where none changed — or null where one
         *  cannot be. */
        private List<Proposition> at(List<Proposition> parts) {
            List<Proposition> out = new ArrayList<>();
            boolean changed = false;
            for (Proposition part : parts) {
                Proposition on = at(part);
                if (on == null) {
                    return null;
                }
                changed |= on != part;
                out.add(on);
            }
            return changed ? out : parts;
        }
    }

    /** What a part that cannot be put comes to, told apart from every part by identity. */
    private static final Proposition CANNOT = new Proposition.Always(false);

    /**
     * {@code form} with {@code element} at {@code there} in every remainder and, where
     * {@code itself}, where it is weighed itself — or null where the exact arithmetic cannot hold
     * that. A remainder left with no number of the input in it is the number it leaves, and one
     * that is left some is moved by whole turns of its divisor, as the remainder of a form of the
     * input's numbers is read.
     */
    private static LinearForm<Quantity> formAt(LinearForm<Quantity> form,
                                               Quantity.OfABinding element,
                                               LinearForm<Quantity> there, boolean itself) {
        List<LinearForm<Quantity>> parts = new ArrayList<>();
        parts.add(LinearForm.constant(form.constant()));
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (itself && each.getKey().equals(element)) {
                LinearForm<Quantity> weighed = there.times(each.getValue()).orNull();
                if (weighed == null) {
                    return null;
                }
                parts.add(weighed);
                continue;
            }
            if (!(each.getKey() instanceof Quantity.RemainderOfADividend remainder)
                    || !remainder.dividend().coefs().containsKey(element)) {
                parts.add(LinearForm.weighing(each.getKey(), each.getValue()));
                continue;
            }
            LinearForm<Quantity> dividend = remainder.dividend().over(atom ->
                    atom.equals(element) ? there : LinearForm.atom(atom));
            if (dividend == null || !dividend.constant().isWhole()
                    || !(dividend.constant().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger whole))) {
                return null;
            }
            ExactRatio moved = ExactRatio.of(whole.mod(remainder.divisor()));
            if (!dividend.coefs().isEmpty()) {
                parts.add(LinearForm.weighing(new Quantity.RemainderOfADividend(
                        remainder.operation(), new LinearForm<>(moved, dividend.coefs()),
                        remainder.divisor()), each.getValue()));
                continue;
            }
            LinearForm<Quantity> left = LinearForm.<Quantity>constant(moved)
                    .times(each.getValue()).orNull();
            if (left == null) {
                return null;
            }
            parts.add(left);
        }
        return LinearForm.sum(parts).orNull();
    }

    /**
     * That {@code element} is one its list holds and comes round to the value {@code step} past
     * the list's start, in turns of {@code every}: at or past the start, at or before the end, and
     * what {@code turnedBy} leaves of how far it is past the start and {@code step} by
     * {@code every} nothing.
     */
    public static Proposition comesRoundTo(TheElementComesRound round, int step) {
        Quantity.OfABinding element = round.element();
        BigInteger every = round.every();
        LinearForm<Quantity> past = pastTheStart(element);
        if (past == null) {
            return new Proposition.Always(false);
        }
        List<Proposition> each = new ArrayList<>(heldByItsList(element));
        if (every.compareTo(BigInteger.ONE) > 0) {
            LinearForm<Quantity> turned = past.minus(LinearForm.constant(ExactRatio.of(step)))
                    .orNull();
            if (turned == null || !turned.constant().isWhole()
                    || !(turned.constant().floor() instanceof ExactAnswer.Held<BigInteger>(
                            BigInteger whole))) {
                return new Proposition.Always(false);
            }
            Quantity.RemainderOfADividend left = new Quantity.RemainderOfADividend(
                    round.turnedBy(), new LinearForm<>(ExactRatio.of(whole.mod(every)),
                            turned.coefs()), every);
            Relation.OneWay<Quantity> none = Relation.OneWay.of(LinearForm.atom(left), Rel.EQ);
            each.add(new Proposition.Compared(new Relation.Affine(none.form(), none.proposition()),
                    none.holds()));
        }
        return Proposition.all(each);
    }

    /** How far {@code element} is past its list's start, or null where that is no form. */
    private static LinearForm<Quantity> pastTheStart(Quantity.OfABinding element) {
        Quantity.AWholeNumberInTurn number =
                (Quantity.AWholeNumberInTurn) element.handed().orElseThrow();
        return LinearForm.atom((Quantity) element).minus(
                TheWholeNumbersAListStartsWith.ofTheInputsNumbers(number.from())).orNull();
    }

    /** That {@code element}, of a list of every whole number between two, is one its list
     *  holds: at or past the list's start, and at or before its end. */
    static List<Proposition> heldByItsList(Quantity.OfABinding element) {
        Quantity.AWholeNumberInTurn number =
                (Quantity.AWholeNumberInTurn) element.handed().orElseThrow();
        LinearForm<Quantity> past = pastTheStart(element);
        LinearForm<Quantity> before = TheWholeNumbersAListStartsWith.ofTheInputsNumbers(
                number.to()).minus(LinearForm.atom(element)).orNull();
        if (past == null || before == null) {
            return List.of(new Proposition.Always(false));
        }
        return List.of(atOrAbove(past), atOrAbove(before));
    }

    /**
     * How many elements apart {@code stated} comes out the same, beside its list holding the
     * element ({@link #heldByItsList}) — or nothing where, apart from that, it is no statement that
     * comes round ({@link TheElementComesRound#in}). A row asked it at some element is then
     * answered by the first value the list holds of each turn: every later one of the turn the
     * list holds comes out as that one.
     */
    public static Optional<BigInteger> comesOutAlikeEvery(Proposition stated,
                                                          Quantity.OfABinding element) {
        List<Proposition> held = heldByItsList(element);
        List<Proposition> rest = new ArrayList<>();
        conjunctsOf(stated).forEach(each -> {
            if (!held.contains(each)) {
                rest.add(each);
            }
        });
        return TheElementComesRound.in(Proposition.all(rest))
                .filter(round -> round.element().equals(element))
                .map(TheElementComesRound::every);
    }

    private static List<Proposition> conjunctsOf(Proposition stated) {
        if (!(stated instanceof Proposition.All all)) {
            return List.of(stated);
        }
        List<Proposition> out = new ArrayList<>();
        all.parts().forEach(each -> out.addAll(conjunctsOf(each)));
        return out;
    }

    /** That {@code form} is at or above nought. */
    private static Proposition atOrAbove(LinearForm<Quantity> form) {
        if (form.coefs().isEmpty()) {
            return new Proposition.Always(form.constant().signum() >= 0);
        }
        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, Rel.GE);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds());
    }
}
