package souther.compiler.meaning;

import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.InputNumber;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;

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
     * input put at the value in {@code pinned}.
     */
    public static Remade of(Proposition stated, String head, NewtypeInners inners,
                            Symbols symbols, Map<NumericTerm, ExactRatio> pinned) {
        AnswerAsAnInput reading = new AnswerAsAnInput(head, inners, symbols,
                new LinkedHashMap<>(pinned), false);
        // Remade choice by choice and not count by count: a part about the input alone is left
        // out of one of several things and held of all of them, which comes to something else of
        // a count made of the same statements. So every count is written out first, all of them
        // held to one figure.
        return switch (CountsWrittenOut.of(stated)) {
            case CountsWrittenOut.PastAFigure(CompositionBudget figure) ->
                    new Remade.PastAFigure(figure);
            case CountsWrittenOut.Written(Proposition written) -> {
                Proposition remade = reading.proposition(written);
                yield remade == null ? new Remade.NotAboutTheAnswer() : new Remade.Stated(remade);
            }
        };
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
     * row's as it is, and what is about the answer alone asks nothing of the row. Under a
     * quantifier the values stay inside it, so what some element is asked is asked of one element
     * — its value beside everything else the statement asks of it — and not of the container
     * beside it.
     */
    public static Proposition ofTheRow(Proposition stated, Map<NumericTerm, ExactRatio> pinned) {
        // A count of statements is the choices of which of them hold, every count in the
        // statement written out together and held to one figure. Past it the row is held to the
        // statement as it stands, and whoever asks the row for it says which figure that was
        // ({@link CountsWrittenOut}).
        return switch (CountsWrittenOut.of(stated)) {
            case CountsWrittenOut.Written(Proposition written) -> ofTheRow(written, pinned, true);
            case CountsWrittenOut.PastAFigure _ -> stated;
        };
    }

    /**
     * The same, with {@code positive} saying whether {@code stated} is asked to hold or to fail
     * where it stands.
     *
     * <p>What comes back is held to one contract, and each case below is a condition sufficient
     * for it. Asked to hold: a row meeting what comes back, with an answer meeting what {@link #of}
     * made of {@code stated}, meets {@code stated}. Asked to fail, what comes back is what no place
     * the statement is read at may meet: a row meeting it nowhere, with an answer failing what
     * {@link #of} made of {@code stated}, fails {@code stated} there. A part the answer was
     * composed for is held at the values whichever way it is asked, since which way it comes out
     * is the answer's; a part about the input alone is asked of the row only where the answer was
     * not composed to settle the whole without it.
     *
     * <p>Sufficient, not necessary: what comes back is what a row is composed to, in the words a
     * row is, and a weaker condition the row's words cannot carry — one of several ways an
     * element may be — is no condition a row is composed toward.
     */
    private static Proposition ofTheRow(Proposition stated, Map<NumericTerm, ExactRatio> pinned,
                                        boolean positive) {
        if (!Proposition.aboutAnAnswer(stated)) {
            return stated;
        }
        return switch (stated) {
            // Where every part has to hold, the row meets each. Where they cannot all hold, the
            // answer was composed so that one part about it fails at the values, and which one is
            // the answer's: so the row holds every value, and that part fails whatever the parts
            // about the input alone come to — said as no place holding one of them away from its
            // value.
            case Proposition.All all -> {
                if (positive) {
                    List<Proposition> parts = ofTheRow(all.parts(), pinned, true);
                    yield parts == null ? null : Proposition.all(parts);
                }
                List<Proposition> away = ofTheRow(all.parts().stream()
                        .filter(part -> !isTheRows(part)).toList(), pinned, false);
                yield away == null ? null : Proposition.any(away);
            }
            case Proposition.Any any -> oneOf(any.parts(), pinned, positive,
                    Proposition::any);
            // Either way it comes out, it answered: the row meets where it does, and what it
            // states the way it is asked.
            case Proposition.WhereItAnswers where -> {
                List<Proposition> parts = new ArrayList<>();
                parts.add(ofTheRow(where.answers(), pinned, true));
                parts.add(ofTheRow(where.states(), pinned, positive));
                yield parts.contains(null) ? null : Proposition.all(parts);
            }
            case Proposition.OnAnApplication applications -> oneOf(applications.each(), pinned,
                    positive, Proposition::onAnApplication);
            case Proposition.SoManyHold _ -> throw new IllegalArgumentException(
                    "a count reaches what a row is held to written out as its choices: " + stated);
            case Proposition.OfTheWays ways -> ofTheRow(ways.written(), pinned, positive);
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
                 Proposition.StringInside _, Proposition.SomeReachable _ ->
                    heldAt(inputNumbersIn(stated), pinned, positive);
            // A statement of the input alone is about no answer, and was returned above.
            case Proposition.Always _, Proposition.Unread _, Proposition.LastToHold _,
                 Proposition.Carried _, Proposition.InTheStrings _ -> stated;
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

    /**
     * What one of {@code parts} holding — joined by {@code joined} — asks of the row.
     *
     * <p>Where it has to hold, the answer was composed for the parts about it ({@link #of}), and
     * which of them holds at the values is the answer's: so the row holds every value they name,
     * and is asked nothing of the parts about the input alone, which the answer did not need.
     * Where it has to fail, every part has to, and the row meets each as it stands.
     */
    private static Proposition oneOf(List<Proposition> parts,
                                     Map<NumericTerm, ExactRatio> pinned, boolean positive,
                                     Function<List<Proposition>, Proposition> joined) {
        if (!positive) {
            List<Proposition> each = ofTheRow(parts, pinned, false);
            return each == null ? null : joined.apply(each);
        }
        List<Proposition> each = ofTheRow(parts.stream().filter(part -> !isTheRows(part))
                .toList(), pinned, true);
        return each == null ? null : Proposition.all(each);
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
         * It holds counts of statements whose choices, written out to remade it choice by choice,
         * are past {@code figure} ({@link CountsWrittenOut}); what the rest of it is about was not
         * looked at past it.
         */
        record PastAFigure(CompositionBudget figure) implements Remade {

            public PastAFigure {
                Objects.requireNonNull(figure, "a statement not remade stopped at some figure");
            }
        }
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
     * first, since which value the answer may be turns on them. In the order the statement names
     * them, which is the order their values are tried in — so one statement is composed for the
     * same pair on every run.
     */
    public static Set<NumericTerm> inputNumbersIn(Proposition stated) {
        AnswerAsAnInput reading = asking(stated);
        return reading == null ? null
                : Collections.unmodifiableSet(new LinkedHashSet<>(reading.inputs));
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
                yield Proposition.compared(new Relation.Affine(one.form(), one.proposition()),
                        one.holds());
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
            // About a position of the input and of no answer, so it is the row's and was set aside
            // above.
            case Proposition.InTheStrings _ -> throw new IllegalStateException(
                    "a statement of the input alone is the row's, and is not read as the answer's: "
                            + stated);
            // Which element of a list the input holds is the last of its key is the row's ({@link
            // #isTheRows}); which element of a list the answer holds is, is the answer's to meet.
            case Proposition.LastToHold(DecisionSubject container, DecisionSubject position,
                                        boolean holds, var _) -> {
                DecisionSubject in = subject(container);
                DecisionSubject by = subject(position);
                yield in == null || by == null ? null
                        : new Proposition.LastToHold(in, by, holds);
            }
            // A search is read from a node of the input, and of no answer; neither is a string
            // inside another, whose strings are values of the input.
            case Proposition.SomeReachable _, Proposition.StringInside _ -> null;
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
            case Proposition.WhereItAnswers where -> {
                Proposition answers = proposition(where.answers());
                Proposition states = proposition(where.states());
                yield answers == null || states == null ? null
                        : Proposition.whereItAnswers(answers, states);
            }
            // A part about the input alone is no way for the answer to meet the whole: which way
            // the row went is the row's, so the answer is held to the parts that are about it
            // ({@link #ofTheRow} holds the row to the values those were composed for).
            case Proposition.Any any -> {
                List<Proposition> parts = propositions(any.parts().stream()
                        .filter(part -> !isTheRows(part)).toList());
                yield parts == null ? null : Proposition.any(parts);
            }
            case Proposition.OnAnApplication applications -> {
                List<Proposition> each = propositions(applications.each());
                yield each == null ? null : Proposition.onAnApplication(each);
            }
            case Proposition.OfTheWays ways -> proposition(ways.written());
            // What a count is about is what its statements are, which its choices name and no
            // more: asked only that, nothing writes them out. Remade, it reaches here written out
            // ({@link #of}).
            case Proposition.SoManyHold counted -> {
                if (!askingWhatItIsAbout) {
                    throw new IllegalArgumentException("a count reaches what is said of an answer"
                            + " written out as its choices: " + stated);
                }
                yield propositions(counted.statements()) == null ? null : counted;
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
            // Every answer is said under one name, so a quantifier over one answer whose element
            // asks of another is two answers under it, which no composer is handed.
            case Proposition.Some some -> {
                DecisionSubject container = subject(some.container());
                Proposition element = proposition(some.ofTheElement());
                yield container == null || element == null
                        || Proposition.Some.quantifiesOver(container, element) ? null
                        : new Proposition.Some(container, element, some.holds());
            }
        };
    }

    /**
     * Whether {@code stated} is a part about the input alone, whatever kind of statement it is.
     *
     * <p>That is the row's to meet and not the answer's, and what {@link #ofTheRow} leaves the row
     * as it is. The row is composed to the way and run, so a part it does not meet is a row that
     * does not reach the rule, and is said as that; held against the answer instead, no value
     * composed for the answer could meet it, and a number of it put at a value here would be a
     * value the row was never held to.
     *
     * <p>Not a part nothing read, nor one holding such a part, which says nothing about whose it
     * is; and not one that holds or fails whatever the row and the answer are.
     */
    private static boolean isTheRows(Proposition stated) {
        return switch (stated) {
            case Proposition.Always _, Proposition.Unread _, Proposition.Carried _ -> false;
            case Proposition.Compared _, Proposition.Truth _, Proposition.InCases _,
                 Proposition.Present _, Proposition.InTheStrings _, Proposition.SameValue _,
                 Proposition.StringInside _, Proposition.LastToHold _,
                 Proposition.SomeReachable _, Proposition.All _, Proposition.Any _,
                 Proposition.OnAnApplication _, Proposition.SoManyHold _, Proposition.Some _,
                 Proposition.WhereItAnswers _, Proposition.OfTheWays _ ->
                    !Proposition.aboutAnAnswer(stated)
                            && !Proposition.leavesSomethingUnread(stated);
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

    /** {@code of} at the input standing for the answer, or null where it is no place of an
     *  answer: a value a case chooses the place of is read off the input's own elements. */
    private Quantity.TheValue value(Quantity.TheValue of) {
        return switch (of) {
            case Quantity.TheValue.AtAPlace(DecisionSubject at) -> {
                DecisionSubject standing = subject(at);
                yield standing == null ? null : new Quantity.TheValue.AtAPlace(standing);
            }
            case Quantity.TheValue.ChosenByCase _ -> null;
        };
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
            case DecisionAtom.ComputedOverAnAnswer computed -> {
                answers.add(computed.list().answered());
                TermPath place = new TermPath(head, computed.list().steps());
                NumericTerm term = hasNoReadingToTakeTheNumberBy() ? new NumericTerm.ValueOf(place)
                        : InputNumber.overWhatWasComputedByPosition(computed.operation(), place,
                                computed.computation(), computed.each(), computed.direction(),
                                inners, symbols);
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
                Quantity.TheValue each = value(different.ofTheElement());
                yield container == null || each == null
                        || !Quantity.HowManyDifferent.oneOfEach(container, each) ? null
                        : new Quantity.HowManyDifferent(container, each);
            }
            case Quantity.HowManyDifferentMeet different -> {
                DecisionSubject container = subject(different.container());
                Quantity.TheValue each = value(different.ofTheElement());
                Proposition stated = proposition(different.meeting().statement());
                yield container == null || each == null || stated == null
                        ? null : Quantity.HowManyDifferentMeet.of(container, each,
                                different.meeting().askedAgainOf(stated));
            }
            case Quantity.HowManyDifferentAcross across -> {
                DecisionSubject container = subject(across.container());
                DecisionSubject each = subject(across.ofTheOccurrence());
                yield container == null || each == null
                        || !each.isAtOrUnder(container.element())
                        || each.howManyContainersHoldIt()
                                != container.howManyContainersHoldIt() + 2 ? null
                        : new Quantity.HowManyDifferentAcross(container, each);
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
            case Quantity.HowManyCarried carried -> throw carried.reachedAReader();
            case Quantity.TheKeptTotal kept -> throw kept.reachedAReader();
            case DecisionAtom.OfTheInput _, Quantity.OfABinding _,
                 Quantity.CodePointsOfAPiece _, Quantity.APieceOf _,
                 Quantity.IsAmongThePieces _, Quantity.RemainderOfADividend _,
                 Quantity.RemainderByAnInput _, Quantity.ProductOfTwo _,
                 Quantity.WhatAnOperationAnswers _, Quantity.HowManyDifferentBelow _ -> null;
        };
    }
}
