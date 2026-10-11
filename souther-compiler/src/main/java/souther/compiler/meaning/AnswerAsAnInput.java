package souther.compiler.meaning;

import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A statement about what one dependency answered, said of the input that stands for that answer
 * while a value is composed for it.
 *
 * <p>What a statement means does not turn on whose value it is about, so it is put in the words a
 * statement about a position of the input is in, and the readers that ask what such a statement
 * asks of a row ask it. A place inside the answer becomes the place of the
 * same path under the name the composed subject gives the whole of the answer; nothing here says
 * what a quantifier, a count or a comparison asks, which is what keeps it from being a second
 * account of those.
 *
 * <p>Only what is about this one answer. A part about the input, about a value the body bound or
 * about a second answer is a part no value composed here can meet, and the whole is not said.
 */
public final class AnswerAsAnInput {

    private final String head;
    private final NewtypeInners inners;
    private final Symbols symbols;
    private final Set<InjectedAnswer> answers = new LinkedHashSet<>();

    private AnswerAsAnInput(String head, NewtypeInners inners, Symbols symbols) {
        this.head = head;
        this.inners = inners;
        this.symbols = symbols;
    }

    /**
     * {@code stated} over the input named {@code head}, or null where some part of it is about
     * something other than the answer.
     */
    public static Proposition of(Proposition stated, String head, NewtypeInners inners,
                                 Symbols symbols) {
        return new AnswerAsAnInput(head, inners, symbols).proposition(stated);
    }

    /**
     * The one evaluation of one dependency {@code stated} is about, or null where it is about
     * none, about two, or about anything beside one answer.
     *
     * <p>Whether a statement can be put to a composer at all, which is asked where the demand is
     * made and answered by the same walk that puts it there, so the two cannot disagree about
     * what a composer is handed.
     */
    public static InjectedAnswer onlyAnswerIn(Proposition stated) {
        AnswerAsAnInput reading = new AnswerAsAnInput("$answer", null, null);
        return reading.proposition(stated) != null && reading.answers.size() == 1
                ? reading.answers.iterator().next() : null;
    }

    private Proposition proposition(Proposition stated) {
        return switch (stated) {
            case Proposition.Always always -> always;
            case Proposition.Unread unread -> unread;
            case Proposition.Compared(Relation relation, boolean holds, var _) -> {
                if (!(relation instanceof Relation.Affine(LinearForm<Quantity> form,
                        var rel))) {
                    yield null;
                }
                LinearForm<Quantity> over = form(form);
                yield over == null ? null : new Proposition.Compared(
                        new Relation.Affine(over, rel), holds);
            }
            case Proposition.Truth(DecisionSubject of, boolean holds, var _) -> {
                DecisionSubject at = subject(of);
                yield at == null ? null : new Proposition.Truth(at, holds);
            }
            case Proposition.InCases(DecisionSubject of, var cases, boolean holds, var _) -> {
                DecisionSubject at = subject(of);
                yield at == null ? null : new Proposition.InCases(at, cases, holds);
            }
            case Proposition.Present(DecisionSubject of, boolean holds, var _) -> {
                DecisionSubject at = subject(of);
                yield at == null ? null : new Proposition.Present(at, holds);
            }
            case Proposition.SameValue(DecisionSubject one, DecisionSubject other,
                                       boolean holds, var _) -> {
                DecisionSubject left = subject(one);
                DecisionSubject right = subject(other);
                yield left == null || right == null ? null
                        : new Proposition.SameValue(left, right, holds);
            }
            case Proposition.All all -> {
                List<Proposition> parts = propositions(all.parts());
                yield parts == null ? null : Proposition.all(parts);
            }
            case Proposition.Any any -> {
                List<Proposition> parts = propositions(any.parts());
                yield parts == null ? null : Proposition.any(parts);
            }
            case Proposition.OnAnApplication applications -> {
                List<Proposition> each = propositions(applications.each());
                yield each == null ? null : Proposition.onAnApplication(each);
            }
            case Proposition.Some some -> {
                DecisionSubject container = subject(some.container());
                Proposition element = proposition(some.ofTheElement());
                yield container == null || element == null ? null
                        : new Proposition.Some(container, element, some.holds());
            }
        };
    }

    private List<Proposition> propositions(List<Proposition> parts) {
        List<Proposition> out = new ArrayList<>();
        for (Proposition each : parts) {
            Proposition one = proposition(each);
            if (one == null) {
                return null;
            }
            out.add(one);
        }
        return out;
    }

    /** The same place as a position of the input standing for the answer, or null for a position
     *  of the behavior's own input. */
    private DecisionSubject subject(DecisionSubject of) {
        if (!(of instanceof DecisionSubject.AnAnswer answer)) {
            return null;
        }
        answers.add(answer.answered());
        return new DecisionSubject.AnInput(new TermPath(head, answer.steps()));
    }

    private LinearForm<Quantity> form(LinearForm<Quantity> form) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            Quantity atom = quantity(each.getKey());
            if (atom == null) {
                return null;
            }
            coefs.merge(atom, each.getValue(), (a, b) -> a.plus(b).orNull());
        }
        return new LinearForm<>(form.constant(), coefs);
    }

    private Quantity quantity(Quantity quantity) {
        return switch (quantity) {
            case DecisionAtom.OfAnAnswer(DecisionSubject.AnAnswer at) -> {
                answers.add(at.answered());
                yield new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(new TermPath(head, at.steps())));
            }
            case DecisionAtom.TakenOfAnAnswer taken -> {
                answers.add(taken.of().answered());
                TermPath place = new TermPath(head, taken.of().steps());
                // Without a reading to take the number by, which is how a statement is only asked
                // whether it can be put to a composer: the place stands for the number.
                NumericTerm term = inners == null ? new NumericTerm.ValueOf(place)
                        : NumericTerm.TakenOf.asItStands(taken.operation(), place,
                                taken.arguments(), taken.at(), inners, symbols);
                yield term == null ? null : new DecisionAtom.OfTheInput(term);
            }
            case Quantity.HowManyMeet count -> {
                DecisionSubject container = subject(count.container());
                Proposition each = proposition(count.ofTheElement());
                yield container == null || each == null ? null
                        : new Quantity.HowManyMeet(container, each);
            }
            case Quantity.HowManyHold held -> {
                List<Proposition> each = propositions(held.each());
                yield each == null ? null : new Quantity.HowManyHold(each);
            }
            case Quantity.HowManyDifferent different -> {
                DecisionSubject container = subject(different.container());
                DecisionSubject each = subject(different.ofTheElement());
                yield container == null || each == null ? null
                        : new Quantity.HowManyDifferent(container, each);
            }
            case Quantity.SumOver sum -> {
                DecisionSubject container = subject(sum.container());
                LinearForm<Quantity> each = form(sum.ofTheElement());
                yield container == null || each == null ? null
                        : new Quantity.SumOver(container, each);
            }
            case DecisionAtom.OfTheInput _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.RemainderOfADividend _ -> null;
        };
    }
}
