package souther.compiler.meaning;

import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

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
    private final Map<NumericTerm, ExactRatio> pinned;
    private final boolean askingWhatItIsAbout;
    private final Set<NumericTerm> inputs = new LinkedHashSet<>();
    private final List<LinearForm<Quantity>> comparisons = new ArrayList<>();

    private AnswerAsAnInput(String head, NewtypeInners inners, Symbols symbols,
                            Map<NumericTerm, ExactRatio> pinned, boolean askingWhatItIsAbout) {
        this.head = head;
        this.inners = inners;
        this.symbols = symbols;
        this.pinned = pinned;
        this.askingWhatItIsAbout = askingWhatItIsAbout;
    }

    /**
     * {@code stated} over the input named {@code head}, with each number of the behavior's own
     * input put at the value in {@code pinned}, or null where some part of it is about something
     * other than the answer and those numbers.
     */
    public static Proposition of(Proposition stated, String head, NewtypeInners inners,
                                 Symbols symbols, Map<NumericTerm, ExactRatio> pinned) {
        return new AnswerAsAnInput(head, inners, symbols, new LinkedHashMap<>(pinned), false)
                .proposition(stated);
    }

    /**
     * A comparison of a form over quantities with nought, as the statement it makes: {@code form}
     * {@code proposition} nought, holding or not as {@code held} says.
     *
     * <p>Made here, where a statement is, for a comparison that was read as a column and is asked of
     * an answer as one.
     */
    public static Proposition ofAComparison(LinearForm<? extends Quantity> form, Rel proposition,
                                            boolean held) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>(form.coefs());
        return Proposition.compared(
                new Relation.Affine(new LinearForm<>(form.constant(), coefs), proposition), held);
    }

    /**
     * The one evaluation of one dependency {@code stated} is about, or null where it is about
     * none, about two, or about anything beside one answer and numbers of the input.
     *
     * <p>Whether a statement can be put to a composer at all, which is asked where the demand is
     * made and answered by the same walk that puts it there, so the two cannot disagree about
     * what a composer is handed.
     */
    public static InjectedAnswer onlyAnswerIn(Proposition stated) {
        AnswerAsAnInput reading = asking(stated);
        return reading != null && reading.answers.size() == 1
                ? reading.answers.iterator().next() : null;
    }

    /**
     * The numbers of the behavior's own input {@code stated} is about besides the answer, or null
     * where it is about something no value composed for one answer can be held to.
     *
     * <p>What a composer is to be told before it is asked: those numbers have to be put at values
     * first, since which value the answer may be turns on them.
     */
    public static Set<NumericTerm> inputNumbersIn(Proposition stated) {
        AnswerAsAnInput reading = asking(stated);
        return reading == null ? null : Set.copyOf(reading.inputs);
    }

    /**
     * Every comparison {@code stated} makes, as the form it compares with nought, said of the input
     * named {@code head} — or null where some part of it is about something no value composed for
     * one answer can be held to.
     *
     * <p>What a search for the numbers of the input puts a statement over: a comparison relates
     * those numbers to places of the answer, and where the answer's places can lie is what says
     * where the numbers are worth putting. The forms are the statement's own and are not read again
     * for what they mean.
     */
    public static List<LinearForm<Quantity>> comparisonsIn(Proposition stated, String head,
                                                           NewtypeInners inners,
                                                           Symbols symbols) {
        AnswerAsAnInput reading = new AnswerAsAnInput(head, inners, symbols, Map.of(), true);
        return reading.proposition(stated) == null ? null : List.copyOf(reading.comparisons);
    }

    private static AnswerAsAnInput asking(Proposition stated) {
        AnswerAsAnInput reading =
                new AnswerAsAnInput("$answer", null, null, Map.of(), true);
        return reading.proposition(stated) == null ? null : reading;
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
                if (over == null) {
                    yield null;
                }
                comparisons.add(over);
                // Every number of it fixed, what is left is a number against nought.
                if (over.coefs().isEmpty()) {
                    yield new Proposition.Always(rel.holds(over.constant().signum()) == holds);
                }
                // Spelled for another input, its atoms come in another order, so the form is turned
                // to face the one way again.
                // And a count held against nought is the statement that some element meets what is
                // counted, which {@link Proposition#compared} is what writes.
                Relation.OneWay<Quantity> one =
                        Relation.OneWay.of(over, holds ? rel : rel.denied());
                yield Proposition.compared(
                        new Relation.Affine(one.form(), one.proposition()), one.holds());
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
            // Which element of a list the input holds is the last of its key: a place of the
            // input and of no answer, which the input that stands for the answer does not have.
            case Proposition.LastToHold _ -> null;
            // A search is read from a node of the input, and of no answer.
            case Proposition.SomeReachable _ -> null;
            case Proposition.Carried carried -> throw carried.handedToAReader();
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

    /**
     * Whether this was made only to ask what a statement is about, with no reading of the types to
     * take a number of an answer by. The place stands for the number then: which statements can be
     * put to a composer does not turn on which number it is.
     */
    private boolean hasNoReadingToTakeTheNumberBy() {
        return inners == null;
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

    /**
     * {@code form} over the input standing for the answer, with each number of the behavior's own
     * input put at the value it was fixed at.
     *
     * <p>A number of the input that is not fixed is no number a value composed for the answer can
     * be held to, and the form is not said — except where this is only asked what the statement is
     * about, and the number is kept to be named.
     */
    private LinearForm<Quantity> form(LinearForm<Quantity> form) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        ExactRatio constant = form.constant();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            if (each.getKey() instanceof DecisionAtom.OfTheInput(NumericTerm term)) {
                ExactRatio value = pinned.get(term);
                if (value != null) {
                    ExactRatio before = constant;
                    constant = each.getValue().times(value).flatMap(before::plus).orNull();
                    if (constant == null) {
                        return null;
                    }
                    continue;
                }
                if (!askingWhatItIsAbout) {
                    return null;
                }
                inputs.add(term);
                coefs.merge(each.getKey(), each.getValue(), (a, b) -> a.plus(b).orNull());
                continue;
            }
            // What an operation answers of numbers of the input is kept as those numbers are,
            // and only while none of them is fixed: what it answers of a fixed value is a value
            // nothing here works out.
            if (each.getKey() instanceof Quantity.WhatAnOperationAnswers answers) {
                List<NumericTerm> madeOf = answers.positionsItIsMadeOf();
                if (!askingWhatItIsAbout || madeOf.stream().anyMatch(pinned::containsKey)) {
                    return null;
                }
                inputs.addAll(madeOf);
                coefs.merge(answers, each.getValue(), (a, b) -> a.plus(b).orNull());
                continue;
            }
            Quantity atom = quantity(each.getKey());
            if (atom == null) {
                return null;
            }
            coefs.merge(atom, each.getValue(), (a, b) -> a.plus(b).orNull());
        }
        return new LinearForm<>(constant, coefs);
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
                NumericTerm term = hasNoReadingToTakeTheNumberBy() ? new NumericTerm.ValueOf(place)
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
            // What each element adds may be a number put at a value here, and a sum of a value is
            // that value times how many elements there are, which is no one quantity.
            case Quantity.SumOver sum -> {
                DecisionSubject container = subject(sum.container());
                LinearForm<Quantity> each = form(LinearForm.atom(sum.ofTheElement()));
                yield container == null || each == null || each.constant().signum() != 0
                        || each.coefs().size() != 1
                        || !ExactRatio.ONE.equals(each.coefs().values().iterator().next())
                        ? null
                        : new Quantity.SumOver(container, each.coefs().keySet().iterator().next());
            }
            case DecisionAtom.OfTheInput _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.RemainderOfADividend _,
                 Quantity.WhatAnOperationAnswers _ -> null;
        };
    }
}
