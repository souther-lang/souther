package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What the conditions of one body decide, as the columns of its decision table.
 *
 * <p>Beside {@link ReachingCuts} and not inside it. That one answers what may safely narrow the
 * region a search looks in, and gives up whole facts to stay safe; this one answers which
 * distinctions a rule turns on, where a fact given up is a column the table admits it cannot say
 * the meaning of. The two questions have different right answers about one condition — a truth
 * narrows no region and is a distinction all the same — so they are asked apart, and what a
 * comparison over the input states is asked of the arithmetic rather than read a second way here.
 *
 * <p>Both halves come back together. A column is what tells one rule from another, and what the
 * same condition states about the input is what a search composes a row against; a reader holding
 * one without the other would have to pair them again from the order two walks happened to answer
 * in.
 *
 * @param states      what every condition of this body states about its input
 * @param subjects    what the body's expressions name that a row can control
 * @param comparisons how a comparison over one of them is read
 */
record DecisionMeanings(ConditionMeanings states, DecisionSubjects subjects,
                        DecisionComparison comparisons) {

    /**
     * One condition of a path: the column it is, and what it states about the input.
     *
     * @param onTheWay what it asks of a row, which is as many things as it asks and one column
     */
    record Read(DecidedCondition answer, List<OnTheWay> onTheWay) {}

    /**
     * What {@code condition} coming out {@code held} decides, one entry per condition consulted.
     *
     * <p>The connective is walked here for the reason {@link DemandReading#stated} walks it: a
     * joined condition coming out the way that gives both halves is both halves having come out
     * that way, and the other composition says one of them failed and names neither. So the two
     * readings meet the same conditions, and a column and the region a row for it is looked for in
     * are about one of them.
     *
     * <p>Null where no row brings the condition out {@code held}, which the reading of the ways
     * does not let through, so it is met only where the two read the condition under different
     * names ({@link DecisionNaming#side} says what that comes to); and nothing for a part the
     * source settles {@code held}, which is no column.
     */
    List<Read> deciding(Condition condition, boolean held) {
        if (condition instanceof Condition.Joined joined
                && joined.how().under(held) == souther.compiler.semantics.ConditionJoin.BOTH) {
            List<Read> left = deciding(joined.left(), held);
            List<Read> right = deciding(joined.right(), held);
            if (left == null || right == null) {
                return null;
            }
            List<Read> out = new ArrayList<>(left);
            out.addAll(right);
            return List.copyOf(out);
        }
        List<OnTheWay> stated = states.stating(condition, held);
        // What the source settles is no distinction the body draws: coming out this way for every
        // row it is no column, and coming out the other way for every row there is no rule down
        // this side at all.
        if (stated.stream().anyMatch(each -> each instanceof OnTheWay.Settled settled
                && !settled.thisWay())) {
            return null;
        }
        List<OnTheWay> asked = asked(stated);
        if (asked.isEmpty()) {
            return List.of();
        }
        return List.of(new Read(oneRelation(asked) && (!(condition instanceof Condition.Truth)
                || oneRelation(asked(states.stating(condition, !held))))
                ? answerOf(condition, asked.getFirst(), held)
                : asOneColumn(condition, held), stated));
    }

    /** What was stated less what the source settles this way, which asks nothing of a row and is
     *  no part of a column. */
    private static List<OnTheWay> asked(List<OnTheWay> stated) {
        return stated.stream().filter(each -> !(each instanceof OnTheWay.Settled)).toList();
    }

    /**
     * Whether what was stated is one thing a column can be read off.
     *
     * <p>Asked of a truth both ways it comes out, because the column is the truth's and the two
     * ways are its two answers. A truth that means a comparison is that comparison's column either
     * way; one that some element meets one way and every element fails the other is a relation
     * only one way round, and a column read off that way would make the two answers of one fork
     * answers to two different questions.
     */
    private static boolean oneRelation(List<OnTheWay> stated) {
        return stated.size() == 1 && switch (stated.getFirst()) {
            case OnTheWay.TakenIn(var _, RowDemand.Relational _),
                 OnTheWay.TakenIn(var _, RowDemand.ATruth _) -> true;
            case OnTheWay.TakenIn(var _, RowDemand.Exists _),
                 OnTheWay.TakenIn(var _, RowDemand.ForAll _),
                 OnTheWay.TakenIn(var _, RowDemand.ForTheRun _) -> false;
            case OnTheWay.Narrowed _, OnTheWay.Declined _,
                 OnTheWay.TakenIn(var _, RowDemand.SoMany _) -> true;
            // One of several ways is no relation, and the column is what the condition states.
            case OnTheWay.OneOf _ -> false;
            // Taken off before a column is read ({@link #asked}): it asks nothing to read one off.
            case OnTheWay.Settled _ -> false;
        };
    }

    /**
     * The column a condition that asks several things of a row is.
     *
     * <p>One, because it is one condition: every element of a list meeting two things is two
     * relations a row is composed against and one distinction the body draws. No relation of them
     * is the column, so it is what the condition states ({@link #columnOf}).
     */
    private DecidedCondition asOneColumn(Condition condition, boolean held) {
        return columnOf(states.statedBy(condition), held, condition.occurrence());
    }

    /**
     * The column {@code stated} is, coming out {@code held}: a comparison or a truth where it is
     * one, and otherwise the statement itself ({@link DecisionCondition.AStatement}).
     *
     * <p>Where part of it was not read, the column is named by the condition that met it, with what
     * stopped each part: a statement only partly read is no column two conditions could share.
     *
     * @param met the condition that met it, which names a column nothing could read
     */
    static DecidedCondition columnOf(Proposition stated, boolean held, ConditionOccurrence met) {
        List<WhyUnread> stops = Proposition.stopsIn(stated);
        if (!stops.isEmpty()) {
            return new DecidedCondition.Unread(new DecisionCondition.AConditionNotRead(met,
                    stops.stream().<WhyNotTaken>map(WhyNotTaken.MeaningUnread::new).toList()),
                    held);
        }
        return switch (stated) {
            case Proposition.Truth(DecisionSubject of, boolean holds, var _) ->
                    new DecidedCondition.Stood(new DecisionCondition.ATruth(of), holds == held);
            case Proposition.Compared(Relation.Ordered(DecisionAtom term, var at, Rel proposition),
                                      boolean holds, var _) -> new DecidedCondition.Compared(
                    new DecisionCondition.AnOrderedComparison(term, at, proposition),
                    holds == held);
            case Proposition.Compared(Relation.Affine(LinearForm<Quantity> form, Rel proposition),
                                      boolean holds, var _) when overDecisionAtoms(form) ->
                    new DecidedCondition.Compared(new DecisionCondition.AComparison(
                            decisionForm(form), proposition), holds == held);
            default -> DecisionCondition.AStatement.of(stated, held);
        };
    }

    /** Whether every quantity {@code form} is over is a number a row controls. */
    private static boolean overDecisionAtoms(LinearForm<Quantity> form) {
        return form.coefs().keySet().stream().allMatch(DecisionAtom.class::isInstance);
    }

    /** {@code form}, every quantity of which is a number a row controls, as a form over them. */
    private static LinearForm<DecisionAtom> decisionForm(LinearForm<Quantity> form) {
        Map<DecisionAtom, ExactRatio> coefs = new LinkedHashMap<>();
        form.coefs().forEach((atom, coef) -> {
            if (atom instanceof DecisionAtom decided) {
                coefs.put(decided, coef);
            }
        });
        return new LinearForm<>(form.constant(), coefs);
    }

    /**
     * One thing on the way, as the column it is.
     *
     * <p>What the arithmetic took in is a comparison and what it narrowed is a position, and both
     * are read straight off. What it declined is where this reading has something of its own to
     * say: a truth of a subject a row controls is a column, and everything else is a condition this
     * compiler read nothing of, which the rule carries as that rather than leaving off.
     */
    private DecidedCondition answerOf(Condition condition, OnTheWay one, boolean held) {
        return switch (one) {
            // That some element meets something is no column over the input's numbers: which
            // element did is nothing a value at one position says. So the condition is the column
            // it is where what it is about is a subject a row controls, and otherwise one this
            // reading has no column for. Only a condition the body asks is read this way, so there
            // is one to ask.
            case OnTheWay.TakenIn(var _, RowDemand.Exists _),
                 OnTheWay.TakenIn(var _, RowDemand.ForAll _),
                 OnTheWay.TakenIn(var _, RowDemand.ForTheRun _) ->
                    asOneColumn(condition, held);
            // Which of two values stands at a position: the truth of that position, whichever
            // spelling asked it, read off the demand and not off the condition again. And what
            // came out is the position's value and not the condition's — `f == false` holding is
            // `f` not holding.
            case OnTheWay.TakenIn(var _, RowDemand.ATruth truth) -> new DecidedCondition.Stood(
                    new DecisionCondition.ATruth(new DecisionSubject.AnInput(truth.at())),
                    truth.held());
            case OnTheWay.TakenIn(var _, RowDemand.Relational(var taken)) -> {
                Rel proposition = taken.rel().orItsDenial();
                DecisionCondition.Comparison column = switch (taken) {
                    case TakenConstraint.Affine affine -> new DecisionCondition.AComparison(
                            DecisionComparison.ofTheInput(affine.form()), proposition);
                    case TakenConstraint.Ordered ordered ->
                            new DecisionCondition.AnOrderedComparison(
                                    new DecisionAtom.OfTheInput(ordered.term()), ordered.at(),
                                    proposition);
                    // A hole is the same column as the equality it denies, which is what makes the
                    // table exclusive: `voucher == "spring"` and `voucher /= "spring"` are one
                    // distinction a body draws, met the two ways a path can meet it.
                    case TakenConstraint.AwayFrom away ->
                            new DecisionCondition.AnOrderedComparison(
                                    new DecisionAtom.OfTheInput(away.term()), away.at(),
                                    proposition);
                };
                yield new DecidedCondition.Compared(column, taken.rel() == proposition);
            }
            // Which case a position is, asked by a condition and not by a fork, or one of several
            // ways: the column is what the condition states.
            case OnTheWay.Narrowed _ when condition != null -> asOneColumn(condition, held);
            case OnTheWay.OneOf _ when condition != null -> asOneColumn(condition, held);
            case OnTheWay.OneOf several -> throw new IllegalArgumentException(
                    "one of several ways is read with the arm it is entering: " + several);
            // An arm's, and read with the fork it is an arm of ({@link #asTheArm}): what the column
            // is turns on the answers the other arms have.
            case OnTheWay.Narrowed narrowed -> throw new IllegalArgumentException(
                    "a narrowing is read as an arm of its fork: " + narrowed);
            // What the arithmetic of the input could not take in is still what the condition
            // states, and that is the column. A fork's arm brings no condition of the boolean
            // grammar, and is read where the arm is ({@link #entering}).
            case OnTheWay.Declined declined -> condition == null
                    ? new DecidedCondition.Unread(new DecisionCondition.AConditionNotRead(
                            declined.condition(), declined.whys()), held)
                    : asOneColumn(condition, held);
            // How many elements meet a statement, which a row is composed for and no column over
            // the input's numbers is: which elements meet it is nothing a value at one position
            // says, so the column is the statement.
            case OnTheWay.TakenIn(var _, RowDemand.SoMany _) when condition != null ->
                    asOneColumn(condition, held);
            // A count is a comparison a condition states, and a fork states none.
            case OnTheWay.TakenIn(var _, RowDemand.SoMany many) -> throw new IllegalArgumentException(
                    "a count is stated by a condition, and a fork brings none: " + many);
            // A condition the source settles is no distinction, and is taken off before a column
            // is asked for, the condition's ({@link #deciding}) and the arm's ({@link #entering})
            // alike.
            case OnTheWay.Settled settled -> throw new IllegalArgumentException(
                    "a condition the source settles is no column: " + settled);
        };
    }

    /**
     * What entering {@code part} of {@code match} decides, and what it states about the input.
     *
     * <p>A fork is not a condition of the boolean grammar, so nothing here reads it as a truth: the
     * arm establishes which case the scrutinee turned out to be, and where that could not be said
     * as a narrowing the column says so.
     *
     * <p>An arm the declarations already decide is no distinction the body draws where every value
     * at the position is the arm's case, and is no column — the answer {@link #deciding} gives a
     * condition the source settles this way. Where no value at the position is the arm's case, the
     * arm is still one the body writes and the column is the case it selects; that no row reaches
     * it is said beside it ({@link OnTheWay.Settled}), and not by leaving the arm without words,
     * which would say this reading fell short of naming it.
     */
    Optional<Read> entering(Core.Match match, int part, InputReads reads,
                            ConditionNumbering numbering) {
        List<OnTheWay> onTheWay = states.entering(match, part, reads, numbering);
        if (onTheWay.size() == 1 && onTheWay.getFirst() instanceof OnTheWay.Settled settled
                && settled.thisWay()) {
            return Optional.empty();
        }
        return Optional.of(asTheArm(match, part, reads, onTheWay));
    }

    /** The column taking arm {@code part} is, where it is one. */
    private Read asTheArm(Core.Match match, int part, InputReads reads, List<OnTheWay> onTheWay) {
        if (onTheWay.size() == 1 && onTheWay.getFirst() instanceof OnTheWay.Narrowed narrowed) {
            TermPath at = narrowed.position();
            // Where the value the fork is on stands: a name read on a value left several cases is
            // the name read at the sum, and not a name under the set of them.
            return new Read(new DecidedCondition.Narrowed(new DecisionCondition.ACase(
                    new DecisionSubject.AnInput(at.narrowedFrom().position()),
                    states.answersOf(match, reads)), at.narrowing()), onTheWay);
        }
        // Where the arithmetic had no position to narrow, the fork may still be on something a row
        // controls; and where the declarations leave the position none of the arm's case, there is
        // a position and nothing to narrow it to. The arm says which cases it turned out to be
        // either way, and the arms of one fork are answers about the one subject — which is what
        // keeps a table from admitting a value that is two cases at once. That no row takes it,
        // where none does, is said by what was met on the way and not by the column.
        DecisionSubject subject = subjects.of(match.scrutinee(), reads);
        CasesLeft narrowing = CasesLeft.selectedBy(match.cases().get(part).pattern());
        if (subject != null && narrowing != null) {
            return new Read(new DecidedCondition.Narrowed(
                    new DecisionCondition.ACase(subject, states.answersOf(match, reads)),
                    narrowing), onTheWay);
        }
        // Otherwise the column is what entering the arm states: which case a value the body
        // computed is of, under what.
        return new Read(columnOf(states.entered(match, part, reads), true, metAt(onTheWay)),
                onTheWay);
    }

    /**
     * What taking arm {@code part} of {@code attempt} decides: what the arm states, the clauses of
     * the invariant it checks read over what it is handed, as the column it is.
     *
     * <p>One per arm because the arms are the answers. The success and each departure are
     * distinctions the body draws, and a rule through one is a rule through none of the others.
     */
    Read attempting(Core.IfConstructed attempt, int part, SourcePos at, InputReads reads,
                    ConditionNumbering numbering) {
        List<OnTheWay> onTheWay = states.attempting(attempt, part, at, reads, numbering);
        return new Read(columnOf(states.entered(attempt, part, reads), true, metAt(onTheWay)),
                onTheWay);
    }

    /**
     * The condition that met an arm, as the way into it names it: which a column the arm's
     * statement could not be read as is named by. Every arm whose statement stops somewhere puts
     * that on the way as declined, so one is there to name it.
     */
    private static ConditionOccurrence metAt(List<OnTheWay> onTheWay) {
        for (OnTheWay each : onTheWay) {
            switch (each) {
                case OnTheWay.Declined declined -> {
                    return declined.condition();
                }
                case OnTheWay.Settled settled -> {
                    return settled.condition();
                }
                case OnTheWay.OneOf several -> {
                    return several.condition();
                }
                case OnTheWay.TakenIn _, OnTheWay.Narrowed _ -> { }
            }
        }
        return null;
    }
}
