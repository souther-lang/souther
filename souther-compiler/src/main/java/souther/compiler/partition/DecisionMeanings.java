package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.numeric.Rel;

import java.util.ArrayList;
import java.util.List;
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
                : asOneColumn(condition, held, asked), stated));
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
                 OnTheWay.TakenIn(var _, RowDemand.ForAll _) -> false;
            case OnTheWay.Narrowed _, OnTheWay.Declined _ -> true;
            // Taken off before a column is read ({@link #asked}): it asks nothing to read one off.
            case OnTheWay.Settled _ -> false;
        };
    }

    /**
     * The column a condition that asks several things of a row is.
     *
     * <p>One, because it is one condition: every element of a list meeting two things is two
     * relations a row is composed against and one distinction the body draws. No relation of them
     * is the column, so it is the condition's own where what it is about is a subject a row
     * controls, and otherwise one this reading has no column for — for that reason, and for
     * whatever stopped a part of it on the way, each kept.
     */
    private DecidedCondition asOneColumn(Condition condition, boolean held, List<OnTheWay> asked) {
        DecidedCondition read = ofASubject(condition, held);
        if (read != null) {
            return read;
        }
        List<WhyNotTaken> whys = new ArrayList<>();
        whys.add(new WhyNotTaken.ProjectionIncomplete(asked.size() == 1
                && asked.getFirst() instanceof OnTheWay.TakenIn(var _, var demand)
                && (demand instanceof RowDemand.Exists || demand instanceof RowDemand.ForAll)
                ? WhyNotTaken.Shape.A_QUANTIFIER_AS_A_COLUMN
                : WhyNotTaken.Shape.SEVERAL_DEMANDS_IN_ONE_COLUMN));
        asked.forEach(each -> {
            if (each instanceof OnTheWay.Declined declined) {
                whys.addAll(declined.whys());
            }
        });
        return new DecidedCondition.Unread(new DecisionCondition.AConditionNotRead(
                condition.occurrence(), whys), held);
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
                 OnTheWay.TakenIn(var _, RowDemand.ForAll _) ->
                    asOneColumn(condition, held, List.of(one));
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
            // An arm's, and read with the fork it is an arm of ({@link #asTheArm}): what the column
            // is turns on the answers the other arms have.
            case OnTheWay.Narrowed narrowed -> throw new IllegalArgumentException(
                    "a narrowing is read as an arm of its fork: " + narrowed);
            case OnTheWay.Declined declined -> {
                // A fork brings no condition of the boolean grammar, and what it is about was
                // asked where the arm is.
                DecidedCondition read = condition == null ? null : ofASubject(condition, held);
                yield read != null ? read
                        : new DecidedCondition.Unread(new DecisionCondition.AConditionNotRead(
                                declined.condition(), declined.whys()), held);
            }
            // A condition the source settles is no distinction, and is taken off before a column
            // is asked for, the condition's ({@link #deciding}) and the arm's ({@link #entering})
            // alike.
            case OnTheWay.Settled settled -> throw new IllegalArgumentException(
                    "a condition the source settles is no column: " + settled);
        };
    }

    /**
     * The column {@code condition} is where what it is about is a subject a row controls, or null.
     *
     * <p>Where the arithmetic of the input declined, which is where this reading has something of
     * its own to say: the truth of such a subject, and a comparison over what one of them answered.
     * A condition of any other shape is one this compiler read nothing of.
     */
    private DecidedCondition ofASubject(Condition condition, boolean held) {
        return switch (condition) {
            case Condition.Truth truth -> subjects.truthOf(truth.value(), held, truth.reads());
            case Condition.Compares compares ->
                    comparisons.of(compares.comparison(), compares.reads(), held);
            case Condition.Joined _ -> null;
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
        OnTheWay onTheWay = states.entering(match, part, reads, numbering);
        if (onTheWay instanceof OnTheWay.Settled settled && settled.thisWay()) {
            return Optional.empty();
        }
        return Optional.of(asTheArm(match, part, reads, onTheWay));
    }

    /** The column taking arm {@code part} is, where it is one. */
    private Read asTheArm(Core.Match match, int part, InputReads reads, OnTheWay onTheWay) {
        if (onTheWay instanceof OnTheWay.Narrowed narrowed) {
            TermPath at = narrowed.position();
            // Where the value the fork is on stands: a name read on a value left several cases is
            // the name read at the sum, and not a name under the set of them.
            return new Read(new DecidedCondition.Narrowed(new DecisionCondition.ACase(
                    new DecisionSubject.AnInput(at.narrowedFrom().position()),
                    states.answersOf(match, reads)), at.narrowing()), List.of(onTheWay));
        }
        if (!(onTheWay instanceof OnTheWay.Declined || onTheWay instanceof OnTheWay.Settled)) {
            return new Read(answerOf(null, onTheWay, true), List.of(onTheWay));
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
                    narrowing), List.of(onTheWay));
        }
        return new Read(switch (onTheWay) {
            case OnTheWay.Settled settled -> new DecidedCondition.Unread(
                    new DecisionCondition.AConditionNotRead(settled.condition(),
                            new WhyNotTaken.ProjectionIncomplete(
                                    WhyNotTaken.Shape.AN_ARM_READ_AS_WRITTEN)), true);
            case OnTheWay.Declined _, OnTheWay.Narrowed _, OnTheWay.TakenIn _ ->
                    answerOf(null, onTheWay, true);
        }, List.of(onTheWay));
    }

    /**
     * What taking arm {@code part} of {@code attempt} decides: a column this reading names and
     * cannot say the meaning of, one per arm.
     *
     * <p>One per arm because the arms are the answers. The success and each departure are
     * distinctions the body draws, and a rule through one is a rule through none of the others.
     */
    Read attempting(Core.IfConstructed attempt, int part, SourcePos at,
                    ConditionNumbering numbering) {
        OnTheWay onTheWay = states.attempting(attempt, part, at, numbering);
        return new Read(answerOf(null, onTheWay, true), List.of(onTheWay));
    }
}
