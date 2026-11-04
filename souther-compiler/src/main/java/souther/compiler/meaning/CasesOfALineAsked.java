package souther.compiler.meaning;

import souther.compiler.partition.CompositionBudget;

import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
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
 * worked out in them at that figure. Where a part chosen so far that no row is in leaves the cases
 * past it out — asking where a line decides, and asking the cases some row may be in — the ways
 * are not counted: most of them are past such a part, and the steps bound the rest.
 *
 * <p><b>Counted by the step, and stopped short as a stop.</b> Every step of the choosing is counted
 * against {@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN} for the one case they were said as:
 * each alternative taken and each part asked. Counted by the questions alone, the alternatives
 * would be walked unbounded where nothing is asked — the cases of a choice nobody took apart, or
 * every way of choosing past the last question allowed — and those are as many as the product of
 * the choices. Where the steps run out the choosing stops there, and says the figures it met and,
 * of what it did not walk to, only what is written in the cases already: that some were never
 * taken apart, and the figure each stopped at. And where the cases were never taken apart nothing
 * is asked of them at all. Either way what was not walked is neither a case the line turns in nor
 * one it does not, and the cases already shown to divide rows are what they are beside it.
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
     * @param notWorkedOut every figure some case was stopped at, where some was: which way those
     *                   cases go was not worked out, and empty where every case was
     */
    public record Found(List<DecidingCase> decidesIn, Set<CompositionBudget> notWorkedOut) {

        public Found {
            decidesIn = DecidingCase.eachByItsOwnCondition(decidesIn);
            notWorkedOut = notWorkedOut.isEmpty() ? Set.of()
                    : Collections.unmodifiableSet(EnumSet.copyOf(notWorkedOut));
        }
    }

    private static final Found IN_NONE = new Found(List.of(), Set.of());

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
     * A line whose values in a case are what the case's own statements on them keep them to, and
     * nothing else in the case: a line on a quantity every region leaves the same values. Whether
     * rows in a case stand on both sides of it then turns on two things only, whether a row is in
     * the case and what those statements keep, which asking a case by its statements says
     * ({@link #everyCaseWithARowDivides}).
     */
    public interface KeptByItsStatements {

        /** What {@code part}, one part a case holds, says of the line's values. */
        Keeping keeping(Proposition part);

        /**
         * Whether rows stand on each side of the line in a case that holds a row and whose
         * statements on the line's values are {@code statements}, each of the parts joined a part
         * it holds ({@link Keeping#ITSELF}): what {@link Crossing#MAY_CROSS} says of such a case.
         */
        boolean divides(Proposition statements);
    }

    /** What one part of a case says of the line's values. */
    public enum Keeping {

        /** Nothing: no statement inside it is about them. */
        NOTHING,

        /** It is a statement on them, which keeps them to the side it holds on. */
        ITSELF,

        /** Some statement inside it is, held with others, which choices may leave standing as a
         *  part of its own. */
        INSIDE
    }

    private final Function<Proposition, Crossing> crossedIn;

    /** What keeps the line's values in a case, where its statements alone do; null otherwise. */
    private final KeptByItsStatements kept;

    private int left = CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum();

    /** Each case shown to divide rows, as the conjunction of what it chose. */
    private final Set<Proposition> dividing = new LinkedHashSet<>();

    /** Whether some case was shown to hold rows that do not stand on each side of the line: the
     *  case asked is then not what the line decides in, as it was said. */
    private boolean droppedNonDividing;

    private final Set<CompositionBudget> stopped = EnumSet.noneOf(CompositionBudget.class);

    /** Whether what the choosing was for is answered, so that nothing more is chosen. */
    private boolean enough;

    /** The figures each case was never taken apart at, for the cases already asked of. */
    private final Map<DecidingCase.Cases, Set<CompositionBudget>> figuresOf =
            new IdentityHashMap<>();

    private CasesOfALineAsked(Function<Proposition, Crossing> crossedIn,
                              KeptByItsStatements kept) {
        this.crossedIn = crossedIn;
        this.kept = kept;
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
        return new CasesOfALineAsked(crossedIn, null).asked(said);
    }

    /**
     * The same, of a line whose values in a case are what the case's own statements on them keep
     * them to ({@link KeptByItsStatements}): where every case with a row in it is shown to hold one
     * on each side, the case is what it was said as, and no case is chosen.
     */
    public static Found casesOf(DecidingCase said, Function<Proposition, Crossing> crossedIn,
                                KeptByItsStatements kept) {
        return new CasesOfALineAsked(crossedIn, Objects.requireNonNull(kept)).asked(said);
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
    public record Atoms<T>(List<Atom<T>> each, Set<CompositionBudget> notWorkedOut) {

        public Atoms {
            each = List.copyOf(each);
            notWorkedOut = notWorkedOut.isEmpty() ? Set.of()
                    : Collections.unmodifiableSet(EnumSet.copyOf(notWorkedOut));
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
     * answers it keeps, and to say each case it kept none of. The steps and the ways of choosing
     * are counted as they are for {@link #casesOf}.
     */
    public static <T> Atoms<T> atomsOf(DecidingCase said, Function<Proposition, T> answer) {
        return new CasesOfALineAsked(_ -> Crossing.MAY_CROSS, null).allAsked(said, answer);
    }

    /**
     * The same, of the cases some row may be in, chosen as {@link #casesOf} chooses them: a part
     * chosen so far that {@code mayHoldARow} shows no row to be in leaves every case past it out,
     * neither walked nor answered, since a case chosen further holds no more rows. So it is the
     * steps and not the ways of choosing that bound the asking, and the cases {@code each} leaves
     * out are those no row is in and those past the steps, which {@code notWorkedOut} says.
     *
     * @param mayHoldARow false only where no row is in the case, and so in none narrower
     */
    public static <T> Atoms<T> atomsOf(DecidingCase said, Function<Proposition, T> answer,
                                       Predicate<Proposition> mayHoldARow) {
        CasesOfALineAsked asking = new CasesOfALineAsked(
                condition -> mayHoldARow.test(condition) ? Crossing.MAY_CROSS : Crossing.NO_ROWS,
                null);
        if (!asking.aStepIsLeft()) {
            asking.pastTheSteps(List.of(said.standsFor()));
            return new Atoms<>(List.of(), asking.stopped);
        }
        if (said.saidAlone()) {
            return new Atoms<>(mayHoldARow.test(said.condition())
                    ? List.of(new Atom<>(said.condition(), answer.apply(said.condition())))
                    : List.of(), Set.of());
        }
        List<Atom<T>> out = new ArrayList<>();
        asking.chosen(SoFar.NOTHING, List.of(heldFirst(said.standsFor())), asking.crossedIn,
                chosen -> out.add(new Atom<>(chosen, answer.apply(chosen))));
        return new Atoms<>(out, asking.stopped);
    }

    private <T> Atoms<T> allAsked(DecidingCase said, Function<Proposition, T> answer) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Atoms<>(List.of(), stopped);
        }
        if (said.saidAlone()) {
            return new Atoms<>(List.of(new Atom<>(said.condition(), answer.apply(said.condition()))),
                    Set.of());
        }
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        if (said.standsFor().waysOfChoosing(most) > most) {
            stopped.add(CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO);
            addFiguresNotTakenApart(said.standsFor());
            return new Atoms<>(List.of(), stopped);
        }
        List<Atom<T>> out = new ArrayList<>();
        chosen(SoFar.NOTHING, List.of(heldFirst(said.standsFor())), _ -> Crossing.MAY_CROSS,
                chosen -> out.add(new Atom<>(chosen, answer.apply(chosen))));
        return new Atoms<>(out, stopped);
    }

    private Found asked(DecidingCase said) {
        if (!aStepIsLeft()) {
            pastTheSteps(List.of(said.standsFor()));
            return new Found(List.of(), stopped);
        }
        // Said as choices, the cases of a line that decides in more ways than are written out are
        // as many as their product, and the condition holding in some one of them would be as long
        // as they are many. They are not asked as one condition then, but by the condition they
        // were said as, which holds exactly where one of them does; and they are not all asked,
        // since a prefix with no row on one side of the line leaves every case past it unasked,
        // and the steps bound the rest.
        long most = CompositionBudget.CASES_A_LINE_IS_TAKEN_APART_INTO.maximum();
        if (crossedIn.apply(said.standsFor().holdingInSome(most).orElse(said.condition()))
                != Crossing.MAY_CROSS) {
            return IN_NONE;
        }
        if (said.saidAlone()) {
            return new Found(List.of(said), Set.of());
        }
        if (kept != null && everyCaseWithARowDivides(said)) {
            return new Found(List.of(said), Set.of());
        }
        DecidingCase.Cases cases = heldFirst(said.standsFor());
        chosen(SoFar.NOTHING, List.of(cases), crossedIn, chosen -> dividing.add(chosen));
        // Every case with a row in it divides rows and every one was worked out: the case is what
        // it was said as, and saying it again would read the line under another condition for
        // nothing. A case no row is in adds no row to where it holds, so the rows it holds are
        // the rows of the cases the line decides in; one with rows on one side would add rows the
        // line turns nothing between.
        if (!droppedNonDividing && stopped.isEmpty() && !dividing.isEmpty()) {
            return new Found(List.of(said), Set.of());
        }
        return new Found(dividing.stream().map(DecidingCase::alone).toList(), stopped);
    }

    /**
     * Whether every case {@code said} stands for that holds a row holds one on each side of the
     * line, shown without choosing the cases, for a line whose values in a case are what the
     * case's own statements on them keep ({@link KeptByItsStatements}).
     *
     * <p>A case chosen to the end holds, of those statements, the ones the cases it chose hold as
     * parts, less any of them its other choices settle. Nothing else in it says anything of the
     * values: no case holds such a statement inside another statement, which the other choices
     * could leave standing as a part. Fewer statements keep the values to no fewer, so a case
     * whose statements are a set that keeps rows on both sides is one the line decides in wherever
     * a row is in it. So the cases are put with the others holding the same set
     * ({@link #bySetHeld}), and only those whose set keeps the values to one side are asked: chosen
     * as any case is, a prefix no row is in leaving every case past it unasked, until the first
     * of them a row may be in. Where none is, every case with a row in it divides.
     *
     * <p>Asked of the cases holding the set, and not of the cases said with the set beside them:
     * a row meeting a statement of the set may be in a case that does not hold it, which says
     * nothing of the values, and with the statement beside it that row is still there.
     *
     * <p>Where some case of one side may hold a row, a statement is held inside another, the sets
     * are too many to be put together ({@link CompositionBudget#CASES_A_LINE_IS_ASKED_IN} bounds
     * how many each case of several holding together is put with), or the steps ran out on the
     * way, the cases are chosen instead, with what steps are left.
     */
    private boolean everyCaseWithARowDivides(DecidingCase said) {
        List<Proposition> keeping = statementsKeepingTheLine(said.standsFor());
        if (keeping == null || 2 * keeping.size() >= Integer.SIZE - 1
                || 1 << (2 * keeping.size()) > CompositionBudget.CASES_A_LINE_IS_ASKED_IN.maximum()) {
            return false;
        }
        Map<Integer, DecidingCase.Cases> bySet = said.standsFor().fold(bySetHeld(keeping));
        List<DecidingCase.Cases> oneSided = new ArrayList<>();
        bySet.forEach((set, cases) -> {
            List<Proposition> these = new ArrayList<>();
            for (int at = 0; at < keeping.size(); at++) {
                if ((set & 1 << at) != 0) {
                    these.add(keeping.get(at));
                }
            }
            if (!kept.divides(Proposition.all(these))) {
                oneSided.add(cases);
            }
        });
        if (oneSided.isEmpty()) {
            return true;
        }
        // Chosen as any case is, a prefix no row is in leaving every case past it unasked, and
        // the first case with a row in it ends the asking. Cases of two sets may begin alike, and
        // what a prefix comes to is asked of it once.
        boolean[] aRow = {false};
        Map<Proposition, Boolean> noRow = new HashMap<>();
        chosen(SoFar.NOTHING, List.of(heldFirst(new DecidingCase.Cases.EachOf(oneSided))),
                condition -> noRow.computeIfAbsent(condition,
                        asked -> crossedIn.apply(asked) == Crossing.NO_ROWS)
                        ? Crossing.NO_ROWS : Crossing.MAY_CROSS,
                _ -> {
                    aRow[0] = true;
                    enough = true;
                });
        enough = false;
        return !aRow[0] && stopped.isEmpty();
    }

    /**
     * What puts each case of the cases folded with the cases holding the same of {@code keeping}:
     * for each set of them, as the bits of their places in it, the cases that hold as parts that
     * set and no other of them. A set no case holds has no entry.
     *
     * <p>A case of several holding together holds as parts what each of them does, so the cases
     * of a group are those of one entry of each, joined, under the set those entries make
     * together: as many as the sets twice over for each one held, and no more however many ways
     * lead to it.
     */
    private static DecidingCase.Cases.Fold<Map<Integer, DecidingCase.Cases>> bySetHeld(
            List<Proposition> keeping) {
        return new DecidingCase.Cases.Fold<>() {

            @Override
            public Map<Integer, DecidingCase.Cases> one(DecidingCase.Cases.One one) {
                int set = 0;
                for (Proposition part : one.condition() instanceof Proposition.All all
                        ? all.parts() : List.of(one.condition())) {
                    int at = keeping.indexOf(part);
                    if (at >= 0) {
                        set |= 1 << at;
                    }
                }
                return Map.of(set, one);
            }

            @Override
            public Map<Integer, DecidingCase.Cases> eachOf(
                    DecidingCase.Cases.EachOf node,
                    List<Map<Integer, DecidingCase.Cases>> alternatives) {
                Map<Integer, List<DecidingCase.Cases>> out = new LinkedHashMap<>();
                for (Map<Integer, DecidingCase.Cases> each : alternatives) {
                    each.forEach((set, cases) ->
                            out.computeIfAbsent(set, _ -> new ArrayList<>()).add(cases));
                }
                return anyOneOfEach(out);
            }

            @Override
            public Map<Integer, DecidingCase.Cases> together(
                    DecidingCase.Cases.Together node,
                    List<Map<Integer, DecidingCase.Cases>> factors) {
                // The factors chosen so far for each set, written out flat while one way leads to
                // the set, so that they are chosen in the order they were written.
                Map<Integer, List<DecidingCase.Cases>> so = Map.of(0, List.of());
                for (Map<Integer, DecidingCase.Cases> factor : factors) {
                    Map<Integer, List<List<DecidingCase.Cases>>> out = new LinkedHashMap<>();
                    so.forEach((had, before) -> factor.forEach((set, cases) -> {
                        List<DecidingCase.Cases> joined = new ArrayList<>(before);
                        joined.add(cases);
                        out.computeIfAbsent(had | set, _ -> new ArrayList<>()).add(joined);
                    }));
                    Map<Integer, List<DecidingCase.Cases>> next = new LinkedHashMap<>();
                    out.forEach((set, ways) -> next.put(set, ways.size() == 1 ? ways.getFirst()
                            : List.of(new DecidingCase.Cases.EachOf(ways.stream()
                                    .<DecidingCase.Cases>map(DecidingCase.Cases.Together::new)
                                    .toList()))));
                    so = next;
                }
                Map<Integer, DecidingCase.Cases> made = new LinkedHashMap<>();
                so.forEach((set, joined) -> made.put(set, joined.size() == 1 ? joined.getFirst()
                        : new DecidingCase.Cases.Together(joined)));
                return made;
            }

            @Override
            public Map<Integer, DecidingCase.Cases> notTakenApart(
                    DecidingCase.Cases.NotTakenApart notTakenApart) {
                return Map.of(0, notTakenApart);
            }
        };
    }

    /** For each set, any one of the cases holding it. */
    private static Map<Integer, DecidingCase.Cases> anyOneOfEach(
            Map<Integer, List<DecidingCase.Cases>> bySet) {
        Map<Integer, DecidingCase.Cases> out = new LinkedHashMap<>();
        bySet.forEach((set, cases) -> out.put(set, cases.size() == 1 ? cases.getFirst()
                : new DecidingCase.Cases.EachOf(cases)));
        return out;
    }

    /**
     * Every statement on the line's values a case of {@code cases} holds as a part, each once —
     * or null where a case holds one inside another statement, or was never taken apart.
     */
    private List<Proposition> statementsKeepingTheLine(DecidingCase.Cases cases) {
        Set<Proposition> out = new LinkedHashSet<>();
        boolean asParts = cases.fold(new DecidingCase.Cases.Fold<Boolean>() {

            @Override
            public Boolean one(DecidingCase.Cases.One one) {
                for (Proposition part : one.condition() instanceof Proposition.All all
                        ? all.parts() : List.of(one.condition())) {
                    Keeping keeps = kept.keeping(part);
                    if (keeps == Keeping.INSIDE) {
                        return false;
                    }
                    if (keeps == Keeping.ITSELF) {
                        out.add(part);
                    }
                }
                return true;
            }

            @Override
            public Boolean eachOf(DecidingCase.Cases.EachOf node, List<Boolean> alternatives) {
                return !alternatives.contains(false);
            }

            @Override
            public Boolean together(DecidingCase.Cases.Together node, List<Boolean> factors) {
                return !factors.contains(false);
            }

            @Override
            public Boolean notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return false;
            }
        });
        return asParts ? List.copyOf(out) : null;
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
     * @param parts each part chosen, in the order it was, as the others leave it
     */
    private record SoFar(List<Proposition> parts) {

        static final SoFar NOTHING = new SoFar(List.of());

        SoFar {
            parts = List.copyOf(parts);
        }

        /** This, with {@code condition} chosen as well. */
        SoFar and(Proposition condition) {
            List<Proposition> out = new ArrayList<>(parts);
            for (Proposition part : condition instanceof Proposition.All all ? all.parts()
                    : List.of(condition)) {
                Proposition left = part;
                for (Proposition chosen : out) {
                    left = WhereEachLineDecides.given(left, chosen);
                }
                if (left instanceof Proposition.Always(boolean holds) && holds) {
                    continue;
                }
                if (WhereEachLineDecides.isOnePart(left)) {
                    Proposition one = left;
                    out.replaceAll(each -> WhereEachLineDecides.given(each, one));
                }
                out.add(left);
            }
            return new SoFar(out);
        }

        /** The conjunction of what has been chosen. */
        Proposition condition() {
            return Proposition.all(parts);
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
     */
    private void chosen(SoFar chosen, List<DecidingCase.Cases> toChoose,
                        Function<Proposition, Crossing> goesOn, Consumer<Proposition> atEnd) {
        if (enough) {
            return;
        }
        if (toChoose.isEmpty()) {
            atEnd.accept(chosen.condition());
            return;
        }
        List<DecidingCase.Cases> rest = toChoose.subList(1, toChoose.size());
        switch (toChoose.getFirst()) {
            case DecidingCase.Cases.One(var condition) -> {
                if (!aStepIsLeft()) {
                    pastTheSteps(toChoose);
                    return;
                }
                SoFar further = chosen.and(condition);
                // A prefix no row is in leaves no row in any case past it, so none of those is
                // walked or said as one not worked out.
                switch (goesOn.apply(further.condition())) {
                    case MAY_CROSS -> chosen(further, rest, goesOn, atEnd);
                    case CANNOT_CROSS -> droppedNonDividing = true;
                    case NO_ROWS -> { }
                }
            }
            // Every alternative: one that divides rows is no answer about another. Each taken is
            // a step, and where the steps run out the ones not taken are not walked.
            case DecidingCase.Cases.EachOf(var alternatives) -> {
                for (int at = 0; at < alternatives.size(); at++) {
                    if (!aStepIsLeft()) {
                        List<DecidingCase.Cases> notWalked =
                                new ArrayList<>(alternatives.subList(at, alternatives.size()));
                        notWalked.addAll(rest);
                        pastTheSteps(notWalked);
                        return;
                    }
                    List<DecidingCase.Cases> next = new ArrayList<>();
                    next.add(alternatives.get(at));
                    next.addAll(rest);
                    chosen(chosen, next, goesOn, atEnd);
                }
            }
            case DecidingCase.Cases.Together(var factors) -> {
                List<DecidingCase.Cases> next = new ArrayList<>(factors);
                next.addAll(rest);
                chosen(chosen, next, goesOn, atEnd);
            }
            // Nobody took them apart, and nothing asks them.
            case DecidingCase.Cases.NotTakenApart(var stoppedAt) -> stopped.add(stoppedAt);
        }
    }

    /**
     * Out of steps, with {@code notWalked} left: stopped at the steps, and at each figure a case
     * left was stopped at where it was never taken apart.
     *
     * <p>The others are not work this would have done. That the cases were never taken apart was
     * met where they were taken apart, and is written in the cases themselves, so it is read off
     * them as they stand — once over each, and not by choosing among them.
     */
    private void pastTheSteps(List<DecidingCase.Cases> notWalked) {
        stopped.add(CompositionBudget.CASES_A_LINE_IS_ASKED_IN);
        notWalked.forEach(this::addFiguresNotTakenApart);
    }

    /** Adds to what stopped this each figure the cases {@code cases} stand for were stopped at,
     *  where they were never taken apart. Out of steps is where this is asked, so it is asked of
     *  each case once however many times the steps run out: what is asked is a visit to each case
     *  and not a choice among them. */
    private void addFiguresNotTakenApart(DecidingCase.Cases cases) {
        stopped.addAll(cases.notTakenApartAt(figuresOf));
    }

    /** Whether one more step may be taken — an alternative chosen or a part asked — counting it
     *  where it may. */
    private boolean aStepIsLeft() {
        if (left == 0) {
            return false;
        }
        left--;
        return true;
    }
}
