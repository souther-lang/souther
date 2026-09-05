package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.List;

/**
 * What a clause of a behavior states outright, in the order the author wrote it.
 *
 * <p><b>Only what the rule requires.</b> A conjunct is part of what the rule asks of an answer, so
 * whatever it says the rule says; a disjunct is not — {@code id.value > 0 || id.flagged} is
 * satisfied wherever the other side is, whatever the comparison comes to. So the walk descends
 * through {@code &&} and through what a {@code let} binds, which is not a choice either, and stops
 * at everything else.
 *
 * <p><b>One descent, however many readers.</b> Two things are read off what a clause states — the
 * comparisons it draws lines with, and the predicates it tells sets of strings apart with — and
 * each walking the tree for itself would be the connective recognised twice, in two places free to
 * come to different answers about the same {@code &&}. What each reader does with a statement is
 * its own; which statements there are is settled here
 * ({@link souther.compiler.semantics.ConditionJoin}).
 *
 * <p><b>A choice is counted and states nothing.</b> Which statement of a clause a reading is
 * numbered by is what a reader is sent to, so the number may not move with what a reading managed —
 * an {@code ||} takes its place in the order and says neither of its sides. Left out, the statement
 * after it would be numbered as though it were written where the choice is.
 */
final class ClauseStatements {

    private ClauseStatements() {
    }

    /**
     * One of the things a clause states, or the one place it states neither of two.
     *
     * <p>Both are counted: the position in the list is which statement of the clause this is.
     */
    sealed interface Statement {

        /**
         * What the rule states here.
         *
         * @param reads what the names in force at this statement stand for, which is what resolves
         *              a subject to a position. It travels with the statement because a {@code let}
         *              above it binds names the statement is written in
         */
        record States(Core stated, InputReads reads) implements Statement {}

        /** A choice, which states neither of its sides and is here to hold its place in the
         *  numbering. */
        record StatesNeither(Core choice) implements Statement {}
    }

    /** What {@code e} states, read under the names in force at it. */
    static List<Statement> of(Core e, InputReads reads) {
        List<Statement> out = new ArrayList<>();
        walk(e, reads, out);
        return out;
    }

    private static void walk(Core e, InputReads reads, List<Statement> out) {
        // Through what a `let` binds: what the expression comes to is its body, so the body states
        // whatever the rule states. This is the shape a helper called from a clause arrives in —
        // the call expanded and its argument bound to the helper's own parameter — and a walk that
        // stopped here would find the rule stating nothing while the model plainly says something.
        if (e instanceof Core.LetIn let) {
            walk(let.body(), reads.and(let.binder(), let.value()), out);
            return;
        }
        if (e instanceof Core.Binary binary) {
            // Asked once of the connective this is, and every answer read off that. Asked again
            // below, the second question would be free to come to a different answer about the very
            // operator the first has already been read for.
            ConditionJoin joined = ConditionJoin.of(binary.op()).orElse(null);
            if (joined == ConditionJoin.BOTH) {
                walk(binary.left(), reads, out);
                walk(binary.right(), reads, out);
                return;
            }
            if (joined == ConditionJoin.EITHER) {
                out.add(new Statement.StatesNeither(binary));
                return;
            }
        }
        out.add(new Statement.States(e, reads));
    }
}
