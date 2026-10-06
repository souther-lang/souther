package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.core.Core;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Which rules a fork's answer turns on, following only what the library says it does.
 *
 * <p>A rule written somewhere inside what a fork tests is a rule the fork tests only where the
 * value it decides reaches the fork's answer. {@code List.any(p, xs)} turns on what {@code p}
 * answered, and so the rules {@code p} states are what a fork on it tests.
 *
 * <p><b>Along declared edges and never down the tree.</b> A walk that went wherever it could go
 * would credit a fork with every rule written below it — and a rule credited to a fork it says
 * nothing about is a fork this compiler did not read reported as one it did. What an operation's
 * answer turns on is a fact about the operation
 * ({@link souther.compiler.semantics.OperationFact.TurnsOnWhetherAnArgumentHolds}), so it is asked
 * there.
 *
 * <p><b>And never into a rule.</b> A truth that states a comparison is a rule of its own, and what
 * is inside it is what that comparison is read from — its reading's to take apart, and not parts
 * of the fork. A comparison the source wrote and an operation the library says means one
 * ({@link BooleanMeaning#asAComparison}) are one statement, so the walk stops at both: walked into,
 * {@code List.isEmpty(List.filter(p, xs))} would hand the fork whatever {@code p} leaves unread,
 * while {@code List.length(List.filter(p, xs)) == 0} hands it nothing.
 *
 * <p><b>Stopping is the answer, not a gap.</b> An operation the library says nothing about is one
 * this cannot follow, and the walk ends. What that costs is a fork left stating a rule of its own,
 * which leaves the measure open; what following anyway would cost is a model nothing read reported
 * as read to the end, and the two are not the same kind of wrong.
 */
final class WhatAForkTests {

    private WhatAForkTests() {}

    /**
     * The expressions the truth of {@code atom} turns on, each of them one thing a reader could
     * answer for.
     *
     * <p>{@code atom} itself where nothing takes the walk further, since a fork testing a
     * comparison tests that comparison; the parts of it where it is written out of parts; and
     * beyond that whatever the library says the answer turns on, each read the way a condition is.
     *
     * <p><b>The parts and not whether one of them was found.</b> Which of them a reader owns is a
     * question about each of them: a closure answering {@code p.age > 18 && List.contains(0, p.tags)}
     * states a comparison and something nothing here reads, and the fork around the operation
     * states the second whoever owns the first. Answered as "something in there is owned", the
     * second went with the first — and that is the same partial ownership a condition's own parts
     * are cut along, lost one step past the operation.
     *
     * <p><b>And no answer about ownership says only whether.</b> One was, for a reader with a
     * question about the atom rather than about the parts, and every owner that went through it
     * lost the parts again — the whole of what this is for is that they are asked one at a time. A
     * caller wanting to know who owns the atom composes it from the parts, where the composing is
     * written down. Which answers the atom can give is another question, and
     * {@link TruthOutcomes} answers it.
     *
     * <p><b>The names read as that answer reads them.</b> Both are handed what the names stand for
     * ({@link WhatNamesStandFor}) and neither keeps an account of its own, so a closure handed the
     * elements of a list written out is walked knowing they are written: a part of it that asks
     * the same thing every time is not offered here, beside a part that varies or not.
     */
    static List<Core> partsOfTheAnswer(Core atom, WhatNamesStandFor names) {
        List<Core> out = new ArrayList<>();
        turnsOn(atom, names, new HashMap<>(), out);
        return out;
    }

    /**
     * What a walk found an answer to turn on, said by the walk and not read off what it collected.
     *
     * <p>Three answers, because a walk that collected no part has found one of two different
     * things. A match between {@code false} and {@code true} on a position turns on which case the
     * position holds — the match's own reader classifies that, so nothing is collected here, and the
     * answer still varies. {@code true} turns on nothing at all. Told apart by the count of parts,
     * the first was taken for a walk that stopped, and the operation it was reached from was offered
     * as a rule nobody reads; and the second was taken for the first, and an operation whose answer
     * its container decides was read as one turning on nothing.
     */
    private enum Follow {
        /** Every edge was followed, and the answer varies with what was collected or with which
         *  arm of a choice its own reader classifies. */
        VARIES,
        /** Every edge was followed, and the answer is the same whatever the input. */
        FIXED,
        /** An edge ended somewhere this cannot go past, so what it turns on is not all collected. */
        STOPPED
    }

    private static Follow turnsOn(Core standing, WhatNamesStandFor names,
                                  Map<Asked, Follow> met, List<Core> out) {
        // What an answer turns on does not turn on the type it stands as.
        Core e = Core.withoutStanding(standing);
        if (e == null) {
            return Follow.STOPPED;
        }
        // By what has been asked, which is what makes it stop. The tree is finite and so are the
        // library's edges, and a name a walk followed may lead back to where it started — so a
        // question already asked is one already answered rather than one to ask again. Not a depth:
        // a number would make a walk of thirty-two steps answer and one of thirty-three come back
        // saying nothing was found, which is the shape of an answer nobody decided.
        //
        // A question met again while it is still being answered is one that leads back to itself,
        // and nothing was found on the way round: stopped, which leaves the asker offering itself.
        Asked asked = new Asked(e);
        Follow already = met.putIfAbsent(asked, Follow.STOPPED);
        if (already != null) {
            return already;
        }
        Follow answered = answering(standing, names, met, out);
        met.put(asked, answered);
        return answered;
    }

    private static Follow answering(Core standing, WhatNamesStandFor names,
                                    Map<Asked, Follow> met, List<Core> out) {
        Core e = Core.withoutStanding(standing);
        // Whether it holds is decided by the parts of it that decide it, which is the same cut a
        // fork's own condition is made along ({@link ConditionSkeleton}): a closure answering
        // `a > 0 && b > 0` states two rules, and one written under a name it binds is what the
        // closure answers with. Asked here so that a closure is read the way a condition is,
        // rather than only where its whole body is the rule.
        List<Core> parts = ConditionSkeleton.atoms(e);
        if (parts.size() != 1 || parts.get(0) != e) {
            Follow all = Follow.FIXED;
            for (Core part : parts) {
                all = both(all, turnsOn(part, names, met, out));
            }
            return all;
        }
        // A choice answers with one of its arms, so what it comes to is what they come to and which
        // of them was taken. Both reach the answer: a rule in an arm decides it where that arm is
        // taken, and the condition decides which arm that is. Beside the cut above rather than in
        // it — what a fork tests is one thing however it was computed, and this is the other
        // question, about what deciding it turns on.
        switch (e) {
            case Core.If iff -> {
                return both(turnsOn(iff.cond(), names, met, out),
                        both(turnsOn(iff.then(), names, met, out),
                                turnsOn(iff.els(), names, met, out)));
            }
            // What a match decides by is which case its subject is. That is the match's own
            // reader's to classify and not a part offered here, and an answer chosen by it varies
            // unless the subject is a value the source wrote out.
            case Core.Match match -> {
                Follow all = writtenOut(match.scrutinee(), names) ? Follow.FIXED : Follow.VARIES;
                for (Core.Case arm : match.cases()) {
                    all = both(all, turnsOn(arm.body(), names, met, out));
                }
                return all;
            }
            default -> { }
        }
        // A value the source wrote out turns on nothing: it is an answer and not a question.
        if (writtenOut(e, names)) {
            return Follow.FIXED;
        }
        // What a binding answers is what its body answers.
        if (e instanceof Core.LetIn let) {
            return turnsOn(let.body(), names, met, out);
        }
        // An operation whose answer is the same every time turns on nothing, whatever the library
        // says or does not say about it. Followed as a question instead, one the library says
        // nothing about would be where the walk stopped, and offered as a part that varies. Which
        // answers the application can give is {@link TruthOutcomes}' to say, in either shape the
        // application stands in.
        if (AnOperationApplied.of(e) != null
                && TruthOutcomes.ofTheSide(e, AnswerAspect.TRUTH, names, null).isFixed()) {
            return Follow.FIXED;
        }
        // A truth that states a comparison is a rule, and what the fork turns on there is that
        // rule. Asked of the checker, which says what a truth means, so a comparison the source
        // wrote and an operation meaning one stop at the same place.
        if (BooleanMeaning.asAComparison(e).isPresent()) {
            out.add(e);
            return Follow.VARIES;
        }
        // And beyond an operation the library says the answer turns on, what it turns on.
        Core beyond = beyond(e, names);
        Follow past = beyond == null ? Follow.STOPPED : turnsOn(beyond, names, met, out);
        // A closure is half of what an operation walking a container answers by, and the container
        // is the other half. This walk follows the closure and not the container, so where the
        // closure answers the same whatever it is handed, which answer it is settles which half
        // decides: `List.all(_ -> true, xs)` is true whatever `xs` is, and `List.any(_ -> true, xs)`
        // is whether `xs` holds anything. The first was answered above, as an application the same
        // every time; here the container decides, and the application is what is offered.
        if (past == Follow.FIXED && throughAClosure(e, names)) {
            past = Follow.STOPPED;
        }
        if (past != Follow.STOPPED) {
            return past;
        }
        // Where the walk stopped, the expression is where it stopped and is the thing the answer
        // turns on — which is what a reader is offered to own or to leave.
        out.add(e);
        return Follow.VARIES;
    }

    /** Stopped where either was; otherwise varying where either does, and fixed where both are. */
    private static Follow both(Follow one, Follow other) {
        if (one == Follow.STOPPED || other == Follow.STOPPED) {
            return Follow.STOPPED;
        }
        return one == Follow.VARIES || other == Follow.VARIES ? Follow.VARIES : Follow.FIXED;
    }

    /**
     * Whether {@code e} is a value the source wrote out, which is an answer and not a question.
     *
     * <p>An arm of a choice may be a value rather than a test — {@code if p then true else false} —
     * and what the answer turns on there is which arm was taken and not the values the arms are.
     * Offered as a part, such a value is one nobody answers for and nobody can: it states nothing
     * and there is nothing about it to read, so a fork over a condition every other part of which
     * was read would come back unread on account of a constant.
     *
     * <p>And a name the reading of the input says stands for a value written out, which is what a
     * closure handed the elements of a list written out reads its parameter as.
     */
    private static boolean writtenOut(Core e, WhatNamesStandFor names) {
        return switch (Core.withoutStanding(e)) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _, Core.ListLit _, Core.Tuple _, Core.OptionSome _,
                 Core.OptionNone _, Core.Construct _ -> true;
            default -> names.writtenOut(e);
        };
    }

    /**
     * What the library says the truth of {@code e} turns on, or null where it says nothing.
     *
     * <p>The argument the answer turns on, whose closure answers what its body comes to — which
     * arrives at what the argument stands for and not at how it was written: a closure named before
     * it is handed over is the block the name was bound to.
     */
    private static Core beyond(Core e, WhatNamesStandFor names) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null) {
            return null;
        }
        ValueName operation = applied.operation();
        var turns = DefaultBoundOperationFacts.get()
                .turnsOnWhetherAnArgumentHolds(operation, AnswerAspect.TRUTH);
        Core handed = turns == null ? null : applied.argument(turns.argument());
        return handed == null ? null : answerOf(handed, names);
    }

    /** Whether what the library says {@code e}'s answer turns on is a closure it was handed. */
    private static boolean throughAClosure(Core e, WhatNamesStandFor names) {
        AnOperationApplied applied = AnOperationApplied.of(e);
        if (applied == null) {
            return false;
        }
        var turns = DefaultBoundOperationFacts.get()
                .turnsOnWhetherAnArgumentHolds(applied.operation(), AnswerAspect.TRUTH);
        Core handed = turns == null ? null : applied.argument(turns.argument());
        return handed != null
                && Core.withoutStanding(names.denotes(handed)) instanceof Core.Block;
    }

    /**
     * What {@code e} answers with: the body of the block, where it is one, and otherwise itself.
     *
     * <p>What a name stands for is asked first, of whoever owns that question. A closure written as
     * a name is the block that name was bound to, so a reading that stopped at the name would say a
     * rule inside it decides nothing — and one model would be read two ways depending on whether the
     * author bound the closure before handing it over.
     */
    private static Core answerOf(Core e, WhatNamesStandFor names) {
        Core stands = names.denotes(e);
        return Core.withoutStanding(stands) instanceof Core.Block block ? block.body() : stands;
    }

    /** One question this walk has been asked: an expression. Told apart by the node itself, so
     *  that two of one shape written twice are two questions — which is what this says, and what
     *  holds it is that whatever collects these asks it. A collection comparing keys by identity
     *  would be answering with the identity of the question rather than of the expression, and a
     *  question built afresh to ask with is a new object every time. */
    private record Asked(Core e) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Asked it && it.e == e;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(e);
        }
    }
}
