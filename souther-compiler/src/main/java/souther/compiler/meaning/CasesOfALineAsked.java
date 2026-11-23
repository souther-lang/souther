package souther.compiler.meaning;

import souther.compiler.observe.Figure;
import souther.compiler.partition.CompositionBudget;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * Which of the cases a condition was said for a line decides in, asked a case at a time.
 *
 * <p>A line decides in a case where a row on each side of it can stand in that case: the two rows
 * then differ in the line alone, and the statement turns between them. Asked of the condition the
 * cases were said as, a row on one side may be in one case and the row on the other side in
 * another, and the line turns nothing between those. So the question is asked of each case, and a
 * line decides in the cases said as one only where it decides in one of them.
 *
 * <p><b>Which cases, and not whether some.</b> A row meets the line only in a case the line turns
 * in. A case the line turns nothing in can still hold one of its points, on the one side its rows
 * are on, and a row there says nothing about the line; kept under the condition said for all of
 * them, it would be counted for the point. So every case is asked, and the ones that divide rows
 * are what the line is read in.
 *
 * <p><b>Of a case and not of the condition.</b> This is not the question whether rows of a region
 * stand on both sides of a line asked of a region made of several: rows that reach a line along one
 * way or another are one set of rows, and there the question is asked of all of them together. Here
 * what is several is where the statement turns, which is a fact about rows in one case at a time.
 *
 * <p><b>A case is asked part by part as it is chosen.</b> What has been chosen so far holds every
 * row a case chosen further holds, so where it holds no row on one side of the line, neither does
 * any case chosen past it, and those are not asked. A narrower region holds no more rows on either
 * side than a wider one, which is what makes stopping there a proof. The converse is not one: rows
 * on both sides of what has been chosen so far may each be in a case of their own further on, so a
 * case is one the line decides in only once it is chosen to the end.
 *
 * <p><b>As what its choices leave of it.</b> A part chosen has come out wherever it stands in the
 * other parts chosen beside it, so a case is asked, and kept, as the parts chosen with each of them
 * put in the others ({@link WhereEachLineDecides#given}). That is the same case: the two hold on
 * the same rows. What it changes is how long the question is, which is what a reader of a case
 * pays for asking it: a condition every case holds, decided by what each case chose, is asked as
 * what the case leaves undecided of it, and a case whose choices decide it is asked without it.
 *
 * <p><b>As many cases as are taken apart, and no more.</b> Where every case is answered, with
 * nothing to leave a case out by, how many ways there are of choosing one is counted off the
 * choices before any is asked ({@link DecidingCase.Cases#waysOfChoosing}), and past
 * {@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO} none is asked: those are more cases
 * than are taken apart, whether they were written out or said as choices, and the line is not
 * worked out in them at that figure. Asking where a line decides counts them too, before the
 * choosing: the cases a line decides in are what its points are read in, and walking more ways than
 * are taken apart to find them costs the line its reading in every one, where an author can say the
 * rows at its points outright. The cases some row may be in are counted so too, whatever is asked
 * of each: a part chosen so far that no row is in leaves the cases past it out, but how many cases
 * are left is not known until they are walked, and a reading of each that walks them is as dear as
 * a line's.
 *
 * <p><b>And the ways its numbers leave.</b> Two comparisons of one number are two choices, and as
 * the choices stand every way of taking them is counted, those no value of the number meets
 * among them. So a line whose ways are more than are taken apart as they stand is taken apart still
 * where the ways no comparison chosen leaves a form no value of are no more than that
 * ({@link NumericallyConsistentWays.Counts#ofTheIntervals}), and asking it ends each way at the
 * part that leaves some number no value — a form's interval or a dividend's remainders — before
 * that part is asked, and whatever the asking would have said of it. The ways walked to the end
 * are then among the ones counted, and the count is what bounds them. Only where a line's cases
 * are asked: an answer for every case is for each case there is.
 *
 * <p>Where the intervals leave more than that, the line is taken apart still where the ways the
 * remainders leave as well are no more than that
 * ({@link NumericallyConsistentWays.Counts#ofTheNumbers}), and it is then walked once from each
 * class of remainders, those no comparison tells apart, of every dividend two of its comparisons
 * leave different remainders of ({@link NumericallyConsistentWays#startingAtEachRemainder}), and
 * only where the ways walked from all the starts together are no more than that
 * ({@link NumericallyConsistentWays.Starts#walked}): a way holding at the remainders of more than
 * one start is walked from each, and the count of ways counts it once. A count
 * bounds the ways walked to the end and not the prefixes asked on the way to them, and walked from
 * nothing chosen, a prefix that takes comparisons of one dividend one at a time is refuted only
 * at the comparison that leaves the dividend no remainder, however many parts were asked between.
 * Walked from one remainder, each of those comparisons is decided before it is a choice, and a
 * way the remainder refutes ends at the first of them. What is left to the steps is the ways the
 * remainders leave, each walked once from each class it holds at. Where no dividend is compared
 * that way, or where its classes are more starts than are walked, or where the ways walked from
 * them are more than are taken apart, the line is cut off as it stands.
 *
 * <p><b>Counted by the step, and stopped short as a stop.</b> Every step of the choosing is counted
 * against {@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN} for the one case they were said as:
 * each alternative taken and each part chosen, asked there or not. Counted by the questions
 * alone, the alternatives would be walked unbounded where nothing is asked — the cases of a
 * choice nobody took apart, or every way of choosing past the last question allowed — and those
 * are as many as the product of the choices. Where the steps run out the choosing stops there,
 * and says the figures it met and, of what it did not walk to, only what is written in the cases
 * already: that some were never taken apart, and the figure each stopped at. And where the cases
 * were never taken apart nothing is asked of them at all. Either way what was not walked is
 * neither a case the line turns in nor one it does not, and the cases already shown to divide
 * rows are what they are beside it.
 *
 * <p>Here, beside where the cases were taken apart, because what a case chosen part by part has
 * chosen so far is a conjunction of the statement's parts, and those are joined where a rule joins
 * them and nowhere else.
 */
public final class CasesOfALineAsked {

    /**
     * What asking found.
     *
     * @param decidesIn  the cases shown to hold a row on each side of the line, each by itself; the
     *                   case asked, as it was said, where every case it stands for is one of them
     *                   or holds no row.
     *                   How many of them a line is read in one by one is the line's to say, over
     *                   every case it holds ({@link DecidingCase#saidInAsFewAsMay})
     * @param notWorkedOutIn the cases asked some of whose cases nobody worked out, each with the
     *                   figures that stopped them; empty where every case was worked out
     * @param walkedPast the case asked, where its cases were more ways of choosing one than are
     *                   taken apart and every one of them was worked out all the same, by the
     *                   ways the numbers leave ({@link WalkedPast}); empty otherwise
     */
    public record Found(List<DecidingCase> decidesIn, List<NotWorkedOut> notWorkedOutIn,
                        List<WalkedPast> walkedPast) {

        public Found {
            decidesIn = DecidingCase.eachByItsOwnCondition(decidesIn);
            notWorkedOutIn = List.copyOf(notWorkedOutIn);
            walkedPast = List.copyOf(walkedPast);
        }

        /** What asking found where no case was worked out past the figure. */
        public Found(List<DecidingCase> decidesIn, List<NotWorkedOut> notWorkedOutIn) {
            this(decidesIn, notWorkedOutIn, List.of());
        }

        /** Every figure some case was stopped at: which way those cases go was not worked out.
         *  Empty where every case was. */
        public Set<Figure.Budget> notWorkedOut() {
            Set<Figure.Budget> out = new LinkedHashSet<>();
            notWorkedOutIn.forEach(each -> out.addAll(each.stoppedAt()));
            return out.isEmpty() ? Set.of() : Collections.unmodifiableSet(out);
        }
    }

    /**
     * A case asked some of whose cases nobody worked out, and what stopped them: the case itself,
     * whose condition every case it stands for holds.
     *
     * <p>The case asked, and not where inside it the choosing stopped. Another case said beside it,
     * shown to divide rows or to divide none, is outside it; a case inside it that was shown either
     * way is not told apart from the ones nobody reached, which is what the case asked leaves open
     * as a whole. Narrower than that would be what was chosen on the way to each stop, and those
     * are as many as the stops; nor are two such cases joined into one, whose condition would be
     * as long as they are many and asked of every row read at the line.
     *
     * <p>And, where they were more ways of choosing one than are taken apart, how many ways they
     * were ({@link CaseCount}), for a reader telling an author why. The count is of every case the
     * case asked stands for, whichever of them were reached, and is no part of why they were not
     * worked out.
     *
     * @param in        the case asked
     * @param stoppedAt the figures its cases were stopped at; one or more
     * @param counted   how many ways of choosing its cases there were, where their number, or the
     *                  questions of the statement they are a line's cases of, is what stopped
     *                  them; empty where none was taken apart for another reason
     */
    public record NotWorkedOut(DecidingCase in, Set<Figure.Budget> stoppedAt,
                               Optional<CaseCount> counted) {

        public NotWorkedOut {
            Objects.requireNonNull(in, "cases nobody worked out are some case's");
            Objects.requireNonNull(counted, "the ways were counted or not");
            if (stoppedAt.isEmpty()) {
                throw new IllegalArgumentException(
                        "cases nobody worked out were stopped at some figure");
            }
            stoppedAt = Set.copyOf(stoppedAt);
        }

        /** The same, with the ways not counted. */
        public NotWorkedOut(DecidingCase in, Set<Figure.Budget> stoppedAt) {
            this(in, stoppedAt, Optional.empty());
        }
    }

    /**
     * A case asked whose cases were more ways of choosing one than are taken apart, and every
     * one of which was worked out: the choices stood past the figure, and what the numbers leave
     * of them did not.
     *
     * <p>No stop, and no part of why a line was or was not worked out. It is what the asking
     * cost, for a reader telling an author where a model is dear to read: how many ways there
     * were, and, where the numbers left more than a walk goes to the end of, the ways it walked
     * ({@link CaseCount}).
     *
     * @param in      the case asked
     * @param counted how many ways of choosing its cases there were
     */
    public record WalkedPast(DecidingCase in, CaseCount counted) {

        public WalkedPast {
            Objects.requireNonNull(in, "cases walked past the figure are some case's");
            Objects.requireNonNull(counted, "and were counted");
        }
    }

    private static final Found IN_NONE = new Found(List.of(), List.of());

    /**
     * What asking a case comes to for the line: three answers, of which only one walks the case
     * further.
     *
     * <p>None of them says a row is there. A way is read as an inclusion, so that rows may stand
     * on each side is what is left where neither of the others was shown, and is all that walks on.
     * The two others both leave the case out. A case whose rows are on one side lets the case
     * asked be said as it was no more, since its rows are rows of the case asked that the line
     * turns nothing between; a case no row is in still lets it, since it adds no row to where
     * the case asked holds. They are told apart because they are different facts: one is about the
     * line, the other about whether any row is in the case at all.
     */
    public enum Crossing {

        /** That rows reaching the line in the case stand on each side of it is not shown not to
         *  be so. */
        MAY_CROSS,

        /** Rows may reach the line in the case, but are shown not to stand on each side of it. */
        CANNOT_CROSS,

        /** The whole way to the line with the case taken in is shown to be one no row takes. */
        NO_ROWS
    }

    /**
     * The questions the cases of every line of one statement are asked together
     * ({@link CompositionBudget#QUESTIONS_A_STATEMENT_IS_ASKED}): each the way to a line with what
     * a case has chosen so far taken in, or what a case taken apart to the end comes to. Those
     * are what asking costs; the steps between them are counted for each case on its own
     * ({@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN}).
     *
     * <p>Once they run out the statement is no more asked of. A question past the last is
     * answered as one nothing was shown of, and the next step is not taken, so a line asked so
     * far is one whose cases were not worked out; and the reader asks the statement again of
     * questions already spent ({@link #spent}), so that every line of it is, and what one line
     * spent decides nothing about another's answer.
     */
    public static final class QuestionsOfAStatement {

        private long left;
        private boolean ranOut;

        private QuestionsOfAStatement(long left) {
            this.left = left;
            this.ranOut = left == 0;
        }

        /** The questions of a statement nothing has been asked of yet. */
        public static QuestionsOfAStatement fresh() {
            return new QuestionsOfAStatement(
                    CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED.maximum());
        }

        /** The questions of a statement that spent them all. */
        public static QuestionsOfAStatement spent() {
            return new QuestionsOfAStatement(0);
        }

        /** Whether some line asked a question past the last. */
        public boolean ranOut() {
            return ranOut;
        }

        /** Whether one more question may be asked, counting it where it may. */
        private boolean ask() {
            if (left == 0) {
                ranOut = true;
                return false;
            }
            left--;
            return true;
        }
    }

    private final Function<Proposition, Crossing> crossedIn;

    private final QuestionsOfAStatement ofTheStatement;

    private int left = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();

    /** Whether a case answered left nothing to ask of the cases chosen after it: none is walked. */
    private boolean settled;

    /** Each case shown to divide rows, as the conjunction of what it chose. */
    private final Set<Proposition> dividing = new LinkedHashSet<>();

    /** Whether some case was shown to hold rows that do not stand on each side of the line: the
     *  case asked is then not what the line decides in, as it was said. */
    private boolean droppedNonDividing;

    /** The figures the asking stopped at, each made where it stopped. */
    private final Set<Figure.Budget> stopped = new LinkedHashSet<>();

    /**
     * Where the choosing has been, once a way has taken a part and met it: what the parts chosen
     * leave of the numbers and what they say besides, and what is yet to choose. Ways that reach
     * the same place choose the same cases past it ({@link #chosen}).
     */
    private final Set<Met> met = new HashSet<>();

    /**
     * What the cases past a part chosen depend on, and nothing of how it was reached.
     *
     * <p>The numbers the parts chosen leave hold the rows every comparison of a form among them
     * leaves, so two ways leaving the same numbers and saying the same besides hold the same rows;
     * what is yet to choose is the same cases when it is the same objects, in the same order.
     *
     * @param numbers what the parts chosen leave each form and dividend
     * @param besides the parts chosen that a state of numbers says nothing of
     * @param toChoose what is yet to be chosen
     */
    private record Met(NumericallyConsistentWays.State numbers, Set<Proposition> besides,
                       List<DecidingCase.Cases> toChoose) {

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Met same) || !numbers.equals(same.numbers)
                    || !besides.equals(same.besides) || toChoose.size() != same.toChoose.size()) {
                return false;
            }
            for (int at = 0; at < toChoose.size(); at++) {
                if (toChoose.get(at) != same.toChoose.get(at)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            int hash = 31 * numbers.hashCode() + besides.hashCode();
            for (DecidingCase.Cases each : toChoose) {
                hash = 31 * hash + System.identityHashCode(each);
            }
            return hash;
        }
    }

    /** How many ways of choosing the cases asked there were, where their number stopped them. */
    private Optional<CaseCount> counted = Optional.empty();

    /** How many ways the cases asked were, where they stood past the figure and were worked out
     *  all the same ({@link WalkedPast}). */
    private Optional<CaseCount> walkedPast = Optional.empty();

    /** The figures each case was never taken apart at, for the cases already asked of. */
    private final Map<DecidingCase.Cases, Set<Figure.Budget>> figuresOf =
            new IdentityHashMap<>();

    private CasesOfALineAsked(Function<Proposition, Crossing> crossedIn,
                              QuestionsOfAStatement ofTheStatement) {
        this.crossedIn = crossedIn;
        this.ofTheStatement = Objects.requireNonNull(ofTheStatement);
    }

    /**
     * Which of the cases {@code said} stands for the line decides in.
     *
     * <p>Where some one of them holds is asked first, as one question: where it holds no row on
     * one side of the line, neither does any one of them, which settles every case at once. Asked
     * of the cases where they were taken apart, and not of the condition they were said as, which
     * says where some one holds only as far as it was said the same way; where they were not, the
     * condition is all that says it.
     *
     * @param crossedIn what rows that reach the line with a condition taken in beside the way to
     *                  it come to ({@link Crossing})
     */
    public static Found casesOf(DecidingCase said, Function<Proposition, Crossing> crossedIn) {
        return casesOf(said, crossedIn, QuestionsOfAStatement.fresh());
    }

    /** The same, as one line of a statement asked in {@code ofTheStatement}. */
    public static Found casesOf(DecidingCase said, Function<Proposition, Crossing> crossedIn,
                                QuestionsOfAStatement ofTheStatement) {
        return new CasesOfALineAsked(crossedIn, ofTheStatement).asked(said);
    }

    /**
     * One case taken apart to the end, and what asking it came to.
     *
     * @param condition the conjunction of what the case chose
     * @param answer    what was asked of that condition
     */
    public record Atom<T>(Proposition condition, T answer) {

        public Atom {
            Objects.requireNonNull(condition, "a case is some condition");
        }
    }

    /**
     * What asking found of every case a condition was said for.
     *
     * @param each         every case taken apart to the end that was walked to, in the order they
     *                     are chosen, each with its answer
     * @param notWorkedOut every figure some case was stopped at, where some was: those cases are
     *                     in none of {@code each}, and empty where every case was walked to
     */
    public record Atoms<T>(List<Atom<T>> each, Set<Figure.Budget> notWorkedOut) {

        public Atoms {
            each = List.copyOf(each);
            notWorkedOut = Set.copyOf(notWorkedOut);
        }
    }

    /**
     * What {@code answer} comes to in each of the cases {@code said} stands for, each asked by
     * itself and none given up on the strength of another.
     *
     * <p>For an answer that is not about one line fixed beforehand: what parts the values a
     * relation settles is read off the rows in a case, and a narrower case can part values that a
     * wider one does not. Nothing is kept or dropped here, so nothing hangs on the answers being
     * the same for a case and for the cases it is part of; it is the caller's to say which of the
     * answers it keeps, and to say each case it kept none of.
     *
     * <p>Of the cases some row may be in, chosen as {@link #casesOf} chooses them: a part chosen
     * so far that {@code mayHoldARow} shows no row to be in, or that leaves some number of the
     * parts chosen before it no value, leaves every case past it out, neither walked nor
     * answered, since a case chosen further holds no more rows. The steps are counted, and the
     * ways of choosing, as they are for {@link #casesOf}; the cases {@code each} leaves out are
     * those no row is in and those past a figure, which {@code notWorkedOut} says.
     *
     * @param mayHoldARow false only where no row is in the case, and so in none narrower
     */
    public static <T> Atoms<T> atomsOf(DecidingCase said, Function<Proposition, T> answer,
                                       Predicate<Proposition> mayHoldARow) {
        return atomsOf(said, answer, mayHoldARow, QuestionsOfAStatement.fresh());
    }

    /** The same, as one line of a statement asked in {@code ofTheStatement}. */
    public static <T> Atoms<T> atomsOf(DecidingCase said, Function<Proposition, T> answer,
                                       Predicate<Proposition> mayHoldARow,
                                       QuestionsOfAStatement ofTheStatement) {
        return new CasesOfALineAsked(
                condition -> mayHoldARow.test(condition) ? Crossing.MAY_CROSS : Crossing.NO_ROWS,
                ofTheStatement).allAsked(said, answer, _ -> false);
    }

    /**
     * What asking for a case with a wanted answer found.
     *
     * @param first        the first such case in the order they are chosen, where one was found
     * @param notWorkedOut every figure some case was stopped at where none was found: empty says
     *                     there is none, and not empty that there may be one among the cases not
     *                     worked out
     */
    public record Some<T>(Optional<Atom<T>> first, Set<Figure.Budget> notWorkedOut) {

        public Some {
            notWorkedOut = Set.copyOf(notWorkedOut);
        }
    }

    /**
     * Whether some case of {@code said} that some row may be in has an answer {@code wanted} says
     * yes to, asked of the cases as {@link #atomsOf(DecidingCase, Function, Predicate)} chooses
     * them and walked no further than the first, as one line of a statement asked in
     * {@code ofTheStatement}.
     */
    public static <T> Some<T> someCaseAnswers(DecidingCase said, Function<Proposition, T> answer,
                                              Predicate<Proposition> mayHoldARow,
                                              Predicate<T> wanted,
                                              QuestionsOfAStatement ofTheStatement) {
        CasesOfALineAsked asking = new CasesOfALineAsked(
                condition -> mayHoldARow.test(condition) ? Crossing.MAY_CROSS : Crossing.NO_ROWS,
                ofTheStatement);
        Atoms<T> walked = asking.allAsked(said, answer, wanted);
        Optional<Atom<T>> found = asking.settled ? Optional.of(walked.each().getLast())
                : Optional.empty();
        return new Some<>(found, found.isPresent() ? Set.of() : walked.notWorkedOut());
    }

    /**
     * Each case of {@code said} no part chosen so far of which {@link #crossedIn} shows no row to
     * be in, with what {@code answer} comes to there, each once however many starts reach it;
     * none past {@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO} ways of choosing one,
     * counted as the numbers leave them ({@link #startsOf}); and none past the first whose
     * answer {@code settles} says yes to.
     */
    private <T> Atoms<T> allAsked(DecidingCase said, Function<Proposition, T> answer,
                                  Predicate<T> settles) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Atoms<>(List.of(), stopped);
        }
        if (said.saidAlone()) {
            Optional<Crossing> crossed = crossing(crossedIn, said.condition());
            if (crossed.isEmpty()) {
                return new Atoms<>(List.of(), stopped);
            }
            if (crossed.get() == Crossing.NO_ROWS) {
                return new Atoms<>(List.of(), Set.of());
            }
            if (!ofTheStatement.ask()) {
                pastTheSteps(List.of());
                return new Atoms<>(List.of(), stopped);
            }
            T answered = answer.apply(said.condition());
            settled = settles.test(answered);
            return new Atoms<>(List.of(new Atom<>(said.condition(), answered)), Set.of());
        }
        Optional<List<NumericallyConsistentWays.State>> starts = startsOf(said);
        if (starts.isEmpty()) {
            return new Atoms<>(List.of(), stopped);
        }
        // A case holding at the remainders of more than one start is walked from each, and is one
        // case: it is answered from the first start that reaches it.
        List<Atom<T>> out = new ArrayList<>();
        Set<Proposition> reachedBefore = new HashSet<>();
        DecidingCase.Cases cases = heldFirst(said.standsFor());
        for (NumericallyConsistentWays.State start : starts.get()) {
            List<Proposition> fromHere = new ArrayList<>();
            chosen(SoFar.NOTHING, start, true, List.of(cases), crossedIn, chosen -> {
                fromHere.add(chosen);
                if (reachedBefore.contains(chosen)) {
                    return;
                }
                // What a case comes to is a question of the statement's, as the way to it is;
                // past the last, no step is left and the walk ends.
                if (!ofTheStatement.ask()) {
                    pastTheSteps(List.of());
                    return;
                }
                T answered = answer.apply(chosen);
                out.add(new Atom<>(chosen, answered));
                settled |= settles.test(answered);
            });
            reachedBefore.addAll(fromHere);
        }
        return new Atoms<>(out, stopped);
    }

    private Found asked(DecidingCase said) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Found(List.of(), notWorkedOutIn(said));
        }
        // Said as choices, the cases of a line that decides in more ways than are written out are
        // as many as their product, and the condition holding in some one of them would be as long
        // as they are many. They are not asked as one condition then, but by the condition they
        // were said as, which holds exactly where one of them does; and they are not all asked,
        // since a prefix with no row on one side of the line leaves every case past it unasked,
        // and the steps bound the rest.
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        Optional<Crossing> inSome = crossing(crossedIn,
                said.standsFor().holdingInSome(most).orElse(said.condition()));
        if (inSome.isEmpty()) {
            return new Found(List.of(), notWorkedOutIn(said));
        }
        if (inSome.get() != Crossing.MAY_CROSS) {
            return IN_NONE;
        }
        if (said.saidAlone()) {
            return new Found(List.of(said), List.of());
        }
        Optional<List<NumericallyConsistentWays.State>> starts = startsOf(said);
        if (starts.isEmpty()) {
            return new Found(List.of(), notWorkedOutIn(said));
        }
        DecidingCase.Cases cases = heldFirst(said.standsFor());
        for (NumericallyConsistentWays.State start : starts.get()) {
            chosen(SoFar.NOTHING, start, true, List.of(cases), crossedIn,
                    chosen -> dividing.add(chosen));
        }
        // Every case with a row in it divides rows and every one was worked out: the case is what
        // it was said as, and saying it again would read the line under another condition for
        // nothing. A case no row is in adds no row to where it holds, so the rows it holds are
        // the rows of the cases the line decides in; one with rows on one side would add rows the
        // line turns nothing between.
        if (!droppedNonDividing && stopped.isEmpty() && !dividing.isEmpty()) {
            return new Found(List.of(said), List.of(), walkedPastBy(said));
        }
        return new Found(dividing.stream().map(DecidingCase::alone).toList(),
                notWorkedOutIn(said), walkedPastBy(said));
    }

    /** The case asked as it was walked past the figure, where it was and no case of it was
     *  stopped: a case stopped is told of by what stopped it ({@link NotWorkedOut}). */
    private List<WalkedPast> walkedPastBy(DecidingCase said) {
        return stopped.isEmpty() && walkedPast.isPresent()
                ? List.of(new WalkedPast(said, walkedPast.get())) : List.of();
    }

    /**
     * What choosing a case of some cases takes first: a part, a choice among alternatives, cases
     * nobody took apart, or nothing at all, which is no step.
     */
    private sealed interface Begins {

        /** A part, {@code condition}. */
        record WithAPart(Proposition condition) implements Begins {}

        /**
         * A choice, each alternative of which takes {@code first} first: a part where it begins
         * with one, and nothing said where it begins with anything else.
         */
        record WithAChoice(List<Optional<Proposition>> first) implements Begins {

            public WithAChoice {
                first = List.copyOf(first);
            }
        }

        /** Cases nobody took apart. */
        record WithAStop() implements Begins {}

        /** Nothing: cases held together that are none. */
        record WithNothing() implements Begins {}
    }

    /** What each case begins with, worked out once for each case however many ways lead to it. */
    private static final DecidingCase.Cases.Fold<Begins> BEGINS = new DecidingCase.Cases.Fold<>() {

        @Override
        public Begins one(DecidingCase.Cases.One one) {
            return new Begins.WithAPart(one.condition());
        }

        @Override
        public Begins eachOf(DecidingCase.Cases.EachOf node, List<Begins> alternatives) {
            return new Begins.WithAChoice(alternatives.stream()
                    .map(each -> each instanceof Begins.WithAPart(var condition)
                            ? Optional.of(condition) : Optional.<Proposition>empty())
                    .toList());
        }

        @Override
        public Begins together(DecidingCase.Cases.Together node, List<Begins> factors) {
            return factors.stream().filter(each -> !(each instanceof Begins.WithNothing))
                    .findFirst().orElse(new Begins.WithNothing());
        }

        @Override
        public Begins notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
            return new Begins.WithAStop();
        }
    };

    /** What each case walked so far begins with ({@link #BEGINS}). */
    private final Map<DecidingCase.Cases, Begins> begins = new IdentityHashMap<>();

    /**
     * Whether the walk takes more than one way past what {@code rest} chooses first: the first
     * thing to choose is a choice two or more of whose alternatives {@code numbers} leaves open, or
     * cases nobody took apart, which end the way. Another part next, or a choice the numbers leave
     * one alternative of, goes on along one way; and nothing left is the end of the way.
     *
     * <p>An alternative is left open unless the part it chooses first is one {@code numbers} has
     * no value left for, which is how the walk ends it.
     */
    private boolean branchesNext(List<DecidingCase.Cases> rest,
                                 NumericallyConsistentWays.State numbers) {
        for (DecidingCase.Cases each : rest) {
            switch (each.fold(BEGINS, begins)) {
                case Begins.WithAPart _ -> {
                    return false;
                }
                case Begins.WithNothing _ -> { }
                case Begins.WithAChoice(var first) -> {
                    return first.stream()
                            .filter(part -> part.isEmpty()
                                    || numbers.takingAll(part.get()) != null)
                            .limit(2).count() > 1;
                }
                case Begins.WithAStop _ -> {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Where the walk of the cases {@code said} stands for starts, each start walked from as the
     * numbers chosen so far leave it: from nothing chosen, where the ways as the choices stand,
     * or as the intervals leave them, are no more than
     * {@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO}; from each class of remainders,
     * where the ways the remainders leave, walked from all of them together, are no more than
     * that. Empty where they are more, which stops the cases at that figure and counts them: they
     * are more cases than are taken apart, and none is asked.
     */
    private Optional<List<NumericallyConsistentWays.State>> startsOf(DecidingCase said) {
        return switch (walkOf(said.standsFor())) {
            case Walk.From(var starts, var pastTheFigure) -> {
                walkedPast = pastTheFigure;
                yield Optional.of(starts);
            }
            case Walk.Past(var ways) -> {
                moreWaysThanAreTakenApart(said);
                counted = Optional.of(ways);
                yield Optional.empty();
            }
        };
    }

    /**
     * How the cases some cases stand for are walked, counted before any is asked
     * ({@link #walkOf}).
     */
    private sealed interface Walk {

        /**
         * From each of {@code starts}; {@code pastTheFigure} counts the ways where the choices
         * stood past the figure and what the numbers leave of them did not ({@link WalkedPast}).
         */
        record From(List<NumericallyConsistentWays.State> starts,
                    Optional<CaseCount> pastTheFigure) implements Walk {

            public From {
                starts = List.copyOf(starts);
                Objects.requireNonNull(pastTheFigure, "the choices stood past the figure or not");
            }
        }

        /** Not at all: they are more ways than are taken apart, as {@code ways} counts them. */
        record Past(CaseCount ways) implements Walk {

            public Past {
                Objects.requireNonNull(ways, "cases past the figure were counted");
            }
        }
    }

    /**
     * How the cases {@code cases} stand for are walked: from nothing chosen, where the ways as the
     * choices stand, or as the intervals leave them, are no more than
     * {@link CompositionBudget#CASES_A_LINE_IS_TAKEN_APART_INTO}; from each class of remainders,
     * where the ways the remainders leave, walked from all of them together, are no more than
     * that; and not at all where they are more.
     */
    private static Walk walkOf(DecidingCase.Cases cases) {
        List<NumericallyConsistentWays.State> nothingChosen =
                List.of(NumericallyConsistentWays.State.NOTHING_CHOSEN);
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        long asTheyStand = cases.waysOfChoosing(most);
        if (asTheyStand <= most) {
            return new Walk.From(nothingChosen, Optional.empty());
        }
        NumericallyConsistentWays.Counts counts = NumericallyConsistentWays.counted(cases);
        if (noMoreThan(counts.ofTheIntervals(), most)) {
            return new Walk.From(nothingChosen,
                    Optional.of(CaseCount.of(cases, counts.ofTheNumbers(), Optional.empty())));
        }
        Optional<NumericallyConsistentWays.Starts> byTheRemainders =
                noMoreThan(counts.ofTheNumbers(), most)
                        ? NumericallyConsistentWays.startingAtEachRemainder(cases)
                        : Optional.empty();
        if (byTheRemainders.isPresent()
                && byTheRemainders.get().walked().compareTo(BigInteger.valueOf(most)) <= 0) {
            return new Walk.From(byTheRemainders.get().states(),
                    Optional.of(CaseCount.of(cases, counts.ofTheNumbers(),
                            Optional.of(byTheRemainders.get().walked()))));
        }
        return new Walk.Past(CaseCount.of(cases, counts.ofTheNumbers(),
                byTheRemainders.map(NumericallyConsistentWays.Starts::walked)));
    }

    /** Whether {@code counted} says there are no more ways than {@code most}. */
    private static boolean noMoreThan(NumericallyConsistentWays.Counted counted, long most) {
        return counted instanceof NumericallyConsistentWays.Counted.AtMost(var ways)
                && ways.compareTo(BigInteger.valueOf(most)) <= 0;
    }

    /** Where the cases of {@code said} nobody worked out are, if there are any: where it holds,
     *  stopped at every figure the asking met ({@link NotWorkedOut}). */
    private List<NotWorkedOut> notWorkedOutIn(DecidingCase said) {
        if (stopped.isEmpty()) {
            return List.of();
        }
        // Cases the statement's questions ran out on were too dear to be asked, as cases past the
        // figure are too many: how many ways they stood for is what a reader is told either way.
        Optional<CaseCount> ways = counted.isPresent() || !ofTheStatement.ranOut() ? counted
                : Optional.of(CaseCount.of(said.standsFor()));
        return List.of(new NotWorkedOut(said, stopped, ways));
    }

    /** The cases of {@code said} were more ways of choosing one than are taken apart: none is
     *  chosen, at that figure and at every figure they were never taken apart at. */
    private void moreWaysThanAreTakenApart(DecidingCase said) {
        stopped.add(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.reached());
        stopped.addAll(said.standsFor().notTakenApartAt(figuresOf));
    }

    /**
     * {@code cases} with what every case of them holds written before the choices, at every depth
     * choosing together is written to.
     *
     * <p>A prefix is walked further only while rows stand on both sides of the line in it, and what
     * is certain to be chosen narrows it from the first alternative on. Chosen last, the parts
     * every case holds are asked once for each way of choosing, and the ones that contradict them
     * are found only at the end of each.
     *
     * <p>Choosing together is associative, so a group written inside a group is the parts of both.
     * What is written under an alternative is held only where the alternative is taken, and stays
     * in it: each alternative is put in this order on its own. The choices keep the order they
     * were written in, since a choice nobody took apart ends the walk there.
     */
    static DecidingCase.Cases heldFirst(DecidingCase.Cases cases) {
        return cases.fold(inThatOrder(cases.references())).cases();
    }

    /**
     * The cases put in that order, with what a group around them is given of them: the parts every
     * case of them holds, and the choices, each in the order they come.
     *
     * @param source  the case that was put in order
     * @param cases   the cases themselves, in that order
     * @param held    the parts every case of them holds, which a group around them holds as well
     * @param choices the choices among them, which a group around them has beside its own
     */
    private record InThatOrder(DecidingCase.Cases source, DecidingCase.Cases cases,
                               List<DecidingCase.Cases> held, List<DecidingCase.Cases> choices) {

        /** Whether a group around this one is given nothing of it. */
        boolean holdsNothing() {
            return held.isEmpty() && choices.isEmpty();
        }
    }

    /**
     * What puts the cases in that order, a case that more than one case holds put in order once.
     *
     * <p>A group inside a group was put in order before the one it is in, so what it holds and
     * what it chooses go into the group around it where they stand — if only one case holds it.
     * A group that more cases hold stays a case of its own in each, and is not copied into them:
     * what is copied is as long as the ways to it, so a group held twice by a group held twice by
     * a group would be written out for every way down. Held by a group, it is chosen from there,
     * and the cases a group stands for are the same either way, since choosing together is
     * associative.
     *
     * @param references how many cases hold each case ({@link DecidingCase.Cases#references})
     */
    private static DecidingCase.Cases.Fold<InThatOrder> inThatOrder(
            Map<DecidingCase.Cases, Integer> references) {
        return new DecidingCase.Cases.Fold<>() {

            @Override
            public InThatOrder one(DecidingCase.Cases.One one) {
                return new InThatOrder(one, one, List.of(one), List.of());
            }

            @Override
            public InThatOrder eachOf(DecidingCase.Cases.EachOf node,
                                      List<InThatOrder> alternatives) {
                DecidingCase.Cases.EachOf each = new DecidingCase.Cases.EachOf(
                        alternatives.stream().map(InThatOrder::cases).toList());
                return new InThatOrder(node, each, List.of(), List.of(each));
            }

            @Override
            public InThatOrder together(DecidingCase.Cases.Together node,
                                        List<InThatOrder> factors) {
                List<DecidingCase.Cases> held = new ArrayList<>();
                List<DecidingCase.Cases> choices = new ArrayList<>();
                for (InThatOrder factor : factors) {
                    if (factor.source() instanceof DecidingCase.Cases.Together
                            && references.get(factor.source()) > 1 && !factor.holdsNothing()) {
                        choices.add(factor.cases());
                    } else {
                        held.addAll(factor.held());
                        choices.addAll(factor.choices());
                    }
                }
                List<DecidingCase.Cases> inOrder = new ArrayList<>(held);
                inOrder.addAll(choices);
                return new InThatOrder(node, new DecidingCase.Cases.Together(inOrder), held,
                        choices);
            }

            @Override
            public InThatOrder notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return new InThatOrder(notTakenApart, notTakenApart, List.of(),
                        List.of(notTakenApart));
            }
        };
    }

    /**
     * What a case has chosen so far, as what its choices leave of it: each part chosen, with every
     * part chosen beside it come out where it stands in the others ({@link WhereEachLineDecides#given}).
     *
     * <p>A part chosen holds in every case past it, so where it stands in another part it has come
     * out already, and the two hold together exactly where the other part with it come out does.
     * What is asked of a case is then as long as what it leaves undecided and not as long as what
     * it was said as: the condition a whole statement of several holds under is held by every case
     * of it and decided by each one's choices, and written beside each it would be asked of the
     * way to every case in full.
     *
     * <p>Each part is kept with what {@link WhereEachLineDecides#given} reads of it: the part it
     * is as one ({@link WhereEachLineDecides#asOnePart}), and every part it holds
     * ({@link WhereEachLineDecides#partsIn}). A part chosen comes out in another only where the
     * other holds it, so a part is put through the others that hold it and no other, and those
     * that hold the part chosen are the only ones put through it: the rest would each be handed
     * back as they are, after a reading of the whole part. And the conjunction is made once, when
     * it is first asked for: a case is asked as it is chosen and kept as it was asked.
     */
    static final class SoFar {

        static final SoFar NOTHING = new SoFar(List.of(), Set.of());

        /**
         * A part chosen, as the others leave it, with what {@link WhereEachLineDecides#given}
         * reads of it.
         *
         * @param part  the part
         * @param asOne the part it is as one, where it is one
         * @param holds every part it holds
         */
        private record Chosen(Proposition part, Optional<WhereEachLineDecides.PartHeld> asOne,
                              Set<WhereEachLineDecides.PartHeld> holds) {

            static Chosen of(Proposition part) {
                return new Chosen(part, WhereEachLineDecides.asOnePart(part),
                        WhereEachLineDecides.partsIn(part));
            }
        }

        /** Each part chosen, in the order it was. */
        private final List<Chosen> parts;

        /** The conjunction of {@link #parts}, once it has been asked for. */
        private Proposition condition;

        /** What has been chosen that a numbers' state says nothing of, as each was said. */
        private final Set<Proposition> besides;

        private SoFar(List<Chosen> parts, Set<Proposition> besides) {
            this.parts = List.copyOf(parts);
            this.besides = besides;
        }

        /** This, with {@code condition} chosen as well. */
        SoFar and(Proposition condition) {
            List<Chosen> out = new ArrayList<>(parts);
            for (Proposition part : condition instanceof Proposition.All all ? all.parts()
                    : List.of(condition)) {
                Chosen left = Chosen.of(part);
                for (Chosen chosen : out) {
                    if (chosen.asOne().isPresent()
                            && left.holds().contains(chosen.asOne().get())) {
                        Proposition met = WhereEachLineDecides.given(left.part(), chosen.part());
                        if (met != left.part()) {
                            left = Chosen.of(met);
                        }
                    }
                }
                if (left.part() instanceof Proposition.Always(boolean holds) && holds) {
                    continue;
                }
                if (left.asOne().isPresent()) {
                    WhereEachLineDecides.PartHeld one = left.asOne().get();
                    for (int at = 0; at < out.size(); at++) {
                        Chosen each = out.get(at);
                        if (each.holds().contains(one)) {
                            Proposition met = WhereEachLineDecides.given(each.part(), left.part());
                            if (met != each.part()) {
                                out.set(at, Chosen.of(met));
                            }
                        }
                    }
                }
                out.add(left);
            }
            return new SoFar(out, besidesWith(condition));
        }

        /**
         * What has been chosen and {@code condition} as well that a numbers' state says nothing
         * of, as each was said: asked before the condition is chosen, since where a way has been
         * met the condition is not.
         */
        Set<Proposition> besidesWith(Proposition condition) {
            Set<Proposition> out = new HashSet<>(besides);
            for (Proposition part : condition instanceof Proposition.All all ? all.parts()
                    : List.of(condition)) {
                if (NumericallyConsistentWays.leavesAStateWhatItHolds(part)) {
                    out.add(part);
                }
            }
            return out;
        }

        /** The conjunction of what has been chosen. */
        Proposition condition() {
            if (condition == null) {
                condition = Proposition.all(parts.stream().map(Chosen::part).toList());
            }
            return condition;
        }
    }

    /**
     * Each case holding all of {@code chosen}, and one case of each of {@code toChoose}, that holds
     * a row on each side of the line — {@code chosen} already shown to.
     *
     * <p>{@code chosen} is the one path walked, taken a part further on the way down, and written
     * out only for a case kept. {@code goesOn} says whether what has been chosen so far is walked
     * further, and {@code atEnd} takes each case chosen to the end.
     *
     * <p>Each prefix is asked with every part chosen. A part about places nothing else asked is
     * about still bears on the answer through whatever the way, the line and the declarations
     * hold of those places together — a relation of the line, a rule of a value around them, a
     * tie a run makes — so the question asked beside it is no question asked without it.
     *
     * <p>But a line's prefix is asked only where the walk is about to take more than one way:
     * before a choice two or more of whose alternatives the numbers chosen so far leave open
     * ({@link #branchesNext}), and at the end of a way. A part chosen where the walk goes on along
     * one way only — the next is another part, or a choice the numbers leave one alternative of —
     * owes its question to the part chosen next, which asks it of everything chosen. Asked
     * there, the narrower prefix holds no more rows on either side than the one put off, so where
     * that one would have ended the way so does this, and no way is walked further than to the
     * next question. What is saved is a reading of the whole way for each such part, where
     * ending the one way there was all it could do. And before any figure is said for cases past
     * a prefix, the question owed for it is asked: a prefix no row is in has no cases past it to
     * say anything of.
     *
     * @param asked whether {@code chosen} has been asked, or a question is owed for it
     */
    private void chosen(SoFar chosen, NumericallyConsistentWays.State numbers, boolean asked,
                        List<DecidingCase.Cases> toChoose, Function<Proposition, Crossing> goesOn,
                        Consumer<Proposition> atEnd) {
        if (settled) {
            return;
        }
        if (toChoose.isEmpty()) {
            if (goesOnPast(chosen, asked, goesOn)) {
                atEnd.accept(chosen.condition());
            }
            return;
        }
        List<DecidingCase.Cases> rest = toChoose.subList(1, toChoose.size());
        switch (toChoose.getFirst()) {
            case DecidingCase.Cases.One(var condition) -> {
                NumericallyConsistentWays.State numbersLeft = numbers.takingAll(condition);
                // A part some form or dividend has no value left for holds no row with what was
                // chosen before it, and is no question: the ways a count of the consistent ones
                // leaves out are the ways the walk does.
                if (numbersLeft == null) {
                    return;
                }
                if (!aStepIsLeft()) {
                    if (goesOnPast(chosen, asked, goesOn)) {
                        pastTheSteps(toChoose);
                    }
                    return;
                }
                // A way that reaches where another has been chooses the same cases past it, in the
                // rows they hold, and those are not walked twice.
                if (!met.add(new Met(numbersLeft.rowsLeft(),
                        chosen.besidesWith(condition), List.copyOf(rest)))) {
                    return;
                }
                SoFar further = chosen.and(condition);
                // A prefix no row is in leaves no row in any case past it, so none of those is
                // walked or said as one not worked out.
                boolean asksNow = branchesNext(rest, numbersLeft);
                if (!asksNow || goesOnPast(further, false, goesOn)) {
                    chosen(further, numbersLeft, asksNow, rest, goesOn, atEnd);
                }
            }
            // Every alternative: one that divides rows is no answer about another. Each taken is
            // a step, and where the steps run out the ones not taken are not walked.
            case DecidingCase.Cases.EachOf(var alternatives) -> {
                for (int at = 0; at < alternatives.size(); at++) {
                    if (!aStepIsLeft()) {
                        if (goesOnPast(chosen, asked, goesOn)) {
                            List<DecidingCase.Cases> notWalked = new ArrayList<>(
                                    alternatives.subList(at, alternatives.size()));
                            notWalked.addAll(rest);
                            pastTheSteps(notWalked);
                        }
                        return;
                    }
                    List<DecidingCase.Cases> next = new ArrayList<>();
                    next.add(alternatives.get(at));
                    next.addAll(rest);
                    chosen(chosen, numbers, asked, next, goesOn, atEnd);
                }
            }
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                chosen(chosen, numbers, asked, next, goesOn, atEnd);
            }
            // Nobody took them apart, and nothing asks them.
            case DecidingCase.Cases.NotTakenApart(var stoppedAt) -> {
                if (goesOnPast(chosen, asked, goesOn)) {
                    stopped.add(stoppedAt);
                }
            }
        }
    }

    /**
     * Whether rows may stand on each side of the line where {@code chosen} holds: so where it has
     * been asked, and otherwise as asking it now says. A case whose rows are on one side is
     * dropped from the case asked as it was said; one no row is in, from nothing.
     */
    private boolean goesOnPast(SoFar chosen, boolean asked,
                               Function<Proposition, Crossing> goesOn) {
        if (asked) {
            return true;
        }
        Optional<Crossing> crossed = crossing(goesOn, chosen.condition());
        if (crossed.isEmpty()) {
            return false;
        }
        return switch (crossed.get()) {
            case MAY_CROSS -> true;
            case CANNOT_CROSS -> {
                droppedNonDividing = true;
                yield false;
            }
            case NO_ROWS -> false;
        };
    }

    /**
     * Out of steps, with {@code notWalked} left: stopped at the steps — the statement's, where they
     * are what ran out, and the case's otherwise — and at each figure a case left was stopped at
     * where it was never taken apart.
     *
     * <p>The others are not work this would have done. That the cases were never taken apart was
     * met where they were taken apart, and is written in the cases themselves, so it is read off
     * them as they stand — once over each, and not by choosing among them.
     */
    private void pastTheSteps(List<DecidingCase.Cases> notWalked) {
        stopped.add(ofTheStatement.ranOut()
                ? CompositionBudget.QUESTIONS_A_STATEMENT_IS_ASKED.reached()
                : CompositionBudget.CASES_A_LINE_IS_ASKED_IN.reached());
        notWalked.forEach(each -> stopped.addAll(each.notTakenApartAt(figuresOf)));
    }

    /** Whether one more step may be taken — an alternative chosen or a part asked — counting it
     *  where it may: none once the statement has no question left. */
    private boolean aStepIsLeft() {
        if (left == 0 || ofTheStatement.ranOut()) {
            return false;
        }
        left--;
        return true;
    }

    /**
     * What rows that reach the line with {@code condition} taken in come to, as {@code goesOn}
     * says: a question of the statement's, and none where no question is left, which stops the
     * asking there at the statement's figure.
     */
    private Optional<Crossing> crossing(Function<Proposition, Crossing> goesOn,
                                        Proposition condition) {
        if (!ofTheStatement.ask()) {
            pastTheSteps(List.of());
            return Optional.empty();
        }
        return Optional.of(goesOn.apply(condition));
    }
}
