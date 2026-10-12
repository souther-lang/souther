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
 * <p>Only what is about this one answer and the input beside it. A number of the input is put at a
 * value before the answer is composed, and the row is held to that value ({@link #ofTheRow}); a
 * part about the input alone is the row's to meet. A part about a value the body bound, about a
 * second answer, or relating the answer to the input by anything but those numbers is a part no
 * value composed here can meet, and the whole is not said.
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

    /**
     * How many choices of which statements hold a comparison remade here is written out as.
     *
     * <p>A number put at a value can leave a count of statements alone against a constant, where
     * the reading that formed the comparison held it to its figure with the number still beside
     * it; so the figure comes with whoever puts numbers at values. A walk that only asks what a
     * statement is about puts none, and a relation keeps the shape its reading held it to.
     */
    private final long mostChoices;
    /** Whether a comparison remade here came to more choices than {@link #mostChoices}. */
    private boolean pastTheFigure;

    private AnswerAsAnInput(String head, NewtypeInners inners, Symbols symbols,
                            Map<NumericTerm, ExactRatio> pinned, boolean askingWhatItIsAbout,
                            long mostChoices) {
        this.head = head;
        this.inners = inners;
        this.symbols = symbols;
        this.pinned = pinned;
        this.askingWhatItIsAbout = askingWhatItIsAbout;
        this.mostChoices = mostChoices;
    }

    /**
     * {@code stated} over the input named {@code head}, with each number of the behavior's own
     * input put at the value in {@code pinned}.
     */
    public static Remade of(Proposition stated, String head, NewtypeInners inners,
                            Symbols symbols, Map<NumericTerm, ExactRatio> pinned,
                            long mostChoices) {
        AnswerAsAnInput reading = new AnswerAsAnInput(head, inners, symbols,
                new LinkedHashMap<>(pinned), false, mostChoices);
        Proposition remade = reading.proposition(stated);
        if (reading.pastTheFigure) {
            return new Remade.PastTheFigure();
        }
        return remade == null ? new Remade.NotAboutTheAnswer() : new Remade.Stated(remade);
    }

    /**
     * What {@code stated} asks of the row while the answer is composed with each number of the
     * input put at its value in {@code pinned}, or null where some number of the input it holds
     * against the answer has no value there.
     *
     * <p>The other half of {@link #of}. A comparison of the answer with numbers of the input is met
     * by the pair, so the row is held to the values the answer was composed for — where the
     * comparison has to hold, each number at its value, and where it has to fail, wherever an
     * element is still asked the rest, at its value too. Everything about the input alone is the
     * row's as it is, and what is about the answer alone asks nothing of the row. So what the row
     * is asked of the element a lookup selects is the selection and the value, together, as one
     * element: asked apart, a row could hold the value at an entry the lookup does not select.
     */
    public static Proposition ofTheRow(Proposition stated, Map<NumericTerm, ExactRatio> pinned) {
        return ofTheRow(stated, pinned, true);
    }

    /** The same, with {@code positive} saying whether {@code stated} is asked to hold or to fail
     *  where it stands. */
    private static Proposition ofTheRow(Proposition stated, Map<NumericTerm, ExactRatio> pinned,
                                        boolean positive) {
        if (!Proposition.aboutAnAnswer(stated)) {
            return stated;
        }
        return switch (stated) {
            case Proposition.All all -> {
                List<Proposition> parts = ofTheRow(all.parts(), pinned, positive);
                yield parts == null ? null : Proposition.all(parts);
            }
            // Where it has to hold, the answer was composed for the parts about it, which is the
            // whole holding whichever way the rest went; where it has to fail, every part has to.
            case Proposition.Any any -> {
                List<Proposition> parts = ofTheRow(positive ? any.parts().stream()
                        .filter(Proposition::aboutAnAnswer).toList() : any.parts(),
                        pinned, positive);
                yield parts == null ? null : Proposition.any(parts);
            }
            case Proposition.OnAnApplication applications -> {
                List<Proposition> each = ofTheRow(applications.each(), pinned, positive);
                yield each == null ? null : Proposition.onAnApplication(each);
            }
            // An element of a container of the input. Where no element may meet it, every element
            // still asked the rest is held at the value, which the answer was composed to fail at.
            case Proposition.Some some when !(some.container()
                    instanceof DecisionSubject.AnAnswer) -> {
                Proposition element = ofTheRow(some.ofTheElement(), pinned,
                        positive == some.holds());
                yield element == null ? null
                        : new Proposition.Some(some.container(), element, some.holds());
            }
            // What the answer is asked, with every number of the input it is asked beside held at
            // the value the answer was composed for — and nothing else of the row, since the rest
            // of it is the answer's to meet.
            case Proposition.Compared _, Proposition.Some _, Proposition.Truth _,
                 Proposition.InCases _, Proposition.Present _, Proposition.SameValue _,
                 Proposition.SomeReachable _ -> heldAt(inputNumbersIn(stated), pinned, positive);
            case Proposition.Always _, Proposition.Unread _, Proposition.LastToHold _,
                 Proposition.Carried _ -> stated;
        };
    }

    /**
     * Each of {@code terms} at its value in {@code pinned} — or, where the part they are named in
     * is to fail, some one of them away from it — or null where one has no value there or there is
     * no such set.
     */
    private static Proposition heldAt(Set<NumericTerm> terms, Map<NumericTerm, ExactRatio> pinned,
                                      boolean positive) {
        if (terms == null) {
            return null;
        }
        List<Proposition> pins = new ArrayList<>();
        for (NumericTerm term : terms) {
            ExactRatio value = pinned.get(term);
            if (value == null) {
                return null;
            }
            pins.add(Proposition.compared(new Relation.Affine(new LinearForm<>(value.negated(),
                    Map.of(new DecisionAtom.OfTheInput(term), ExactRatio.ONE)), Rel.EQ),
                    positive));
        }
        return positive ? Proposition.all(pins) : Proposition.any(pins);
    }

    private static List<Proposition> ofTheRow(List<Proposition> parts,
                                              Map<NumericTerm, ExactRatio> pinned,
                                              boolean positive) {
        List<Proposition> out = new ArrayList<>();
        for (Proposition each : parts) {
            Proposition one = ofTheRow(each, pinned, positive);
            if (one == null) {
                return null;
            }
            out.add(one);
        }
        return out;
    }

    /** What a statement came to with the answer standing as an input. */
    public sealed interface Remade {

        /** The statement, over the input that stands for the answer. */
        record Stated(Proposition statement) implements Remade {}

        /** A part of it is about something other than the answer and the numbers put at
         *  values. */
        record NotAboutTheAnswer() implements Remade {}

        /**
         * A comparison in it came to a count of statements written out as more choices of which
         * of them hold than the figure handed in; what the rest of it is about was not looked at
         * past it.
         */
        record PastTheFigure() implements Remade {}
    }

    /**
     * A comparison of a form over quantities with nought, as the statement it makes: {@code form}
     * {@code proposition} nought, holding or not as {@code held} says.
     *
     * <p>Made here, where a statement is, for a comparison that was read as a column and is asked of
     * an answer as one. Such a form names the answer and a number of the input beside it, and puts
     * neither at a value, so it is never a count of statements alone to be written out as choices.
     */
    public static Proposition ofAComparison(LinearForm<? extends Quantity> form, Rel proposition,
                                            boolean held) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>(form.coefs());
        return Proposition.compared(
                new Relation.Affine(new LinearForm<>(form.constant(), coefs), proposition), held);
    }

    /**
     * The one evaluation of one dependency {@code stated} is about, or null where it is about
     * none, about two, or about anything beside one answer and the input
     * ({@link AnswerAsAnInput}).
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
        AnswerAsAnInput reading = new AnswerAsAnInput(head, inners, symbols, Map.of(), true,
                Long.MAX_VALUE);
        return reading.proposition(stated) == null ? null : List.copyOf(reading.comparisons);
    }

    private static AnswerAsAnInput asking(Proposition stated) {
        AnswerAsAnInput reading =
                new AnswerAsAnInput("$answer", null, null, Map.of(), true, Long.MAX_VALUE);
        return reading.proposition(stated) == null ? null : reading;
    }

    private Proposition proposition(Proposition stated) {
        if (isTheRows(stated)) {
            return new Proposition.Always(true);
        }
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
                Proposition remade = Proposition.compared(
                        new Relation.Affine(one.form(), one.proposition()), one.holds(),
                        mostChoices);
                pastTheFigure |= remade == null;
                yield remade;
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
            // input and of no answer, which is the row's ({@link #isTheRows}).
            case Proposition.LastToHold last -> throw new IllegalStateException(
                    "which element is the last of its key is the row's: " + last);
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
            // A part about the input alone is no way for the answer to meet the whole: which way
            // the row went is the row's, so the answer is held to the parts that are about it
            // ({@link #ofTheRow} holds the row to the values those were composed for).
            case Proposition.Any any -> {
                List<Proposition> about = any.parts().stream()
                        .filter(Proposition::aboutAnAnswer).toList();
                List<Proposition> parts = propositions(about.isEmpty() ? any.parts() : about);
                yield parts == null ? null : Proposition.any(parts);
            }
            case Proposition.OnAnApplication applications -> {
                List<Proposition> each = propositions(applications.each());
                yield each == null ? null : Proposition.onAnApplication(each);
            }
            // Over a container of the input, the element's numbers are put at values with every
            // other number of the input, so what is asked of the answer is what the element asks
            // of it at those values. Whether the row holds such an element is the row's.
            case Proposition.Some some when !(some.container()
                    instanceof DecisionSubject.AnAnswer) -> {
                Proposition element = proposition(some.ofTheElement());
                if (element == null || askingWhatItIsAbout) {
                    yield element == null ? null
                            : new Proposition.Some(some.container(), element, some.holds());
                }
                yield some.holds() ? element : element.denied();
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
     * Whether {@code stated} is a part about the input alone that no number of it is put at a value
     * for: which case, truth or value a position of the input holds, and whether one is there.
     *
     * <p>That is the row's to meet and not the answer's. The row is composed to the way and run, so
     * a part it does not meet is a row that does not reach the rule, and is said as that; held
     * against the answer instead, no value composed for the answer could meet it and the whole
     * statement would be one nothing composes to.
     */
    private static boolean isTheRows(Proposition stated) {
        return switch (stated) {
            case Proposition.Truth _, Proposition.InCases _, Proposition.Present _,
                 Proposition.SameValue _, Proposition.LastToHold _,
                 Proposition.SomeReachable _ -> !Proposition.aboutAnAnswer(stated);
            case Proposition.Always _, Proposition.Unread _, Proposition.Compared _,
                 Proposition.All _, Proposition.Any _, Proposition.OnAnApplication _,
                 Proposition.Some _, Proposition.Carried _ -> false;
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
                if (!weighed(coefs, each.getKey(), each.getValue())) {
                    return null;
                }
                continue;
            }
            // What an operation answers of numbers of the input is kept as those numbers are,
            // where this is only asked what the statement is about: it is no number a value
            // composed for the answer can be held to.
            if (each.getKey() instanceof Quantity.WhatAnOperationAnswers answers) {
                if (!askingWhatItIsAbout) {
                    return null;
                }
                inputs.addAll(answers.positionsItIsMadeOf());
                if (!weighed(coefs, answers, each.getValue())) {
                    return null;
                }
                continue;
            }
            Quantity atom = quantity(each.getKey());
            if (atom == null || !weighed(coefs, atom, each.getValue())) {
                return null;
            }
        }
        return new LinearForm<>(constant, coefs);
    }

    /**
     * Adds {@code weight} to what {@code coefs} weighs {@code atom} by, which two terms read as one
     * number weigh together — false where the sum is no number held, and the form is not one this
     * can write.
     */
    private static boolean weighed(Map<Quantity, ExactRatio> coefs, Quantity atom,
                                   ExactRatio weight) {
        if (!coefs.containsKey(atom)) {
            coefs.put(atom, weight);
            return true;
        }
        ExactRatio sum = coefs.get(atom).plus(weight).orNull();
        if (sum == null) {
            return false;
        }
        coefs.put(atom, sum);
        return true;
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
