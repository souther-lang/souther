package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.ClauseExpr;
import souther.compiler.check.Comparison;
import souther.compiler.check.ConjunctStatements;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.PartId;
import souther.compiler.check.RuleRef;
import souther.compiler.check.StringPredicates;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.ApplicationOrigin;

import java.util.ArrayList;
import java.util.List;

/**
 * What a clause of a behavior states outright, and which kind of rule each of those is.
 *
 * <p><b>Only what the rule requires.</b> A conjunct is part of what the rule asks of an answer, so
 * whatever it says the rule says; a disjunct is not — {@code id.value > 0 || id.flagged} is
 * satisfied wherever the other side is, whatever the comparison comes to. Which parts of a clause
 * are conjuncts, and what a {@code let} binds on the way to them, is the shape's answer
 * ({@link ClauseExpr}, {@link ConjunctStatements}) and not this reader's: it recognises no
 * connective of its own, so an {@code if} written as a conjunction is one here as it is wherever
 * else a clause is read.
 *
 * <p><b>One descent, however many readers.</b> Two things are read off what a clause states — the
 * comparisons it draws lines with, and the predicates it tells sets of strings apart with — and each
 * walking the tree for itself would be the connective recognised twice, in two places free to come
 * to different answers about the same {@code &&}.
 *
 * <p><b>And one owner per statement.</b> Which of the readers a statement belongs to is settled here
 * too, and it is the same answer for everyone. Left to each reader, the question every reader asks
 * is "is this mine", and the only word a reader has for no is its own — so a rule read perfectly
 * well as a set of strings was also reported as a comparison whose form could not be read, and the
 * document said both about one thing the author wrote. Named here, "no reader reads this form" is
 * one arm that one reader answers for, and a reader's silence about a statement of another kind is
 * silence rather than a finding.
 *
 * <p>This is the shape the body already has. There a comparison is read where the catalog named one
 * ({@link ComparisonReadings}), so nothing hands a reader of comparisons an application to make what
 * it can of; here the clause is the catalog.
 *
 * <p><b>A choice is counted and states nothing.</b> Which statement of a clause a reading is
 * numbered by is what a reader is sent to, so the number may not move with what a reading managed —
 * an {@code ||} takes its place in the order and says neither of its sides. Left out, the statement
 * after it would be numbered as though it were written where the choice is.
 *
 * <p><b>A part that is denied is not read.</b> What a denied comparison states is the other side of
 * its line, which no reader here draws, so it is a form nobody read and says where it stands.
 */
final class ClauseStatements {

    private ClauseStatements() {
    }

    /**
     * One of the things a part states, with the name this reading issued for it.
     *
     * <p>The name and not the place in a list. Read off the list by whoever held it, the number is
     * one the caller counted — and a caller that skipped an arm it had nothing to do with, or that
     * carried on counting into the next part, would be numbering the statements of a clause its own
     * way. Issued here, there is one answer to which statement of which part a line came out of.
     */
    record Stated(ClauseStatementId id, Statement statement) {}

    /**
     * One of the things a clause states, said as the kind of rule it is.
     *
     * <p>Every arm is counted: the position in the list is which statement of the clause this is,
     * whatever became of it.
     */
    sealed interface Statement {

        /**
         * A comparison, which draws a line on what it compares.
         *
         * @param reads what the names in force at this statement stand for, which is what resolves
         *              a term to a position. It travels with the statement because a {@code let}
         *              above it binds names the statement is written in
         */
        record Compares(Core stated, InputReads reads, Comparison comparison) implements Statement {}

        /**
         * A predicate over the strings at a position, which tells a set of them from the rest.
         *
         * @param states the argument the rule is about and what the predicate states of it, read
         *               once here and carried. Read again by the reader that publishes it, the two
         *               readings would be free to disagree about what the author wrote
         */
        record TellsStringsApart(Core.PreservedCall stated, InputReads reads,
                                 StringPredicates.Stated states) implements Statement {}

        /** A form no reader of clauses reads. The one arm that is a finding: what the model states
         *  here reached this stage and nothing was made of it. */
        record NotRead(Core stated, InputReads reads) implements Statement {}

        /** A choice, which states neither of its sides and is here to hold its place in the
         *  numbering. Not a finding: what such a rule states is not what either side states, and
         *  reporting it would send an author after a limit of this compiler that is not there. */
        record StatesNeither(Core choice) implements Statement {}
    }

    /**
     * What {@code part} states, read under the names in force at it, each under the name this
     * issues for it.
     *
     * @param part which part of which clause the tree came out of, which is half of what a
     *             statement of it is called. The other half is where the statement stands among
     *             this part's, and it is assigned here and nowhere a reader stands
     */
    static List<Stated> of(PartId<RuleRef.Ensures> part, Core e, InputReads reads,
                           Symbols symbols, DeclarationNewtypes newtypes) {
        List<Statement> found = new ArrayList<>();
        statedBy(e, reads, symbols, newtypes, found);
        List<Stated> out = new ArrayList<>();
        for (int at = 0; at < found.size(); at++) {
            out.add(new Stated(new ClauseStatementId(part, at), found.get(at)));
        }
        return out;
    }

    /** What {@code clause} states, as a clause stated and not denied. */
    private static void statedBy(Core clause, InputReads reads, Symbols symbols,
                                 DeclarationNewtypes newtypes, List<Statement> out) {
        for (ConjunctStatements.Stated each :
                ConjunctStatements.statedBy(ClauseExpr.of(clause, true))) {
            // Through what a `let` binds: what the expression comes to is its body, so the body
            // states whatever the rule states. This is the shape a helper called from a clause
            // arrives in — the call expanded and its argument bound to the helper's own parameter.
            InputReads inside = reads;
            for (ClauseExpr.Scoped crossed : each.crossed()) {
                inside = inside.and(crossed.binding().binder(), crossed.binding().value());
            }
            if (each.said() instanceof ClauseExpr.Leaf leaf) {
                statesOf(leaf, inside, symbols, newtypes, out);
            } else {
                out.add(new Statement.StatesNeither(each.said().written()));
            }
        }
    }

    private static void statesOf(ClauseExpr.Leaf leaf, InputReads reads, Symbols symbols,
                                 DeclarationNewtypes newtypes, List<Statement> out) {
        // What a rule states is the truth it is whatever type it stands as.
        Core written = Core.withoutStanding(leaf.written());
        if (!leaf.positive()) {
            out.add(new Statement.NotRead(written, reads));
            return;
        }
        // A `match` whose every other arm is a written `false` is true only where the value is the
        // case the one arm selects and that arm's body is. The selection is a statement of its own,
        // about the scrutinee, and it is not read: leaving it out would have the rule state less
        // than it does about whatever the scrutinee is made of. The body is a clause read under the
        // names the arm gives, so what it states is found as for any other.
        if (written instanceof Core.Match match) {
            Core.Case only = theOnlyArmThatIsNotFalse(match);
            if (only != null) {
                out.add(new Statement.NotRead(match.scrutinee(), reads));
                statedBy(only.body(),
                        reads.choosing(Choice.Decides.ofCase(match, only), symbols, newtypes),
                        symbols, newtypes, out);
                return;
            }
        }
        out.add(whatItStates(leaf.written(), reads, symbols, newtypes));
    }

    /** The arm of {@code match} that is not a written {@code false}, where there is exactly one and
     *  every other arm is; null otherwise. */
    private static Core.Case theOnlyArmThatIsNotFalse(Core.Match match) {
        Core.Case only = null;
        for (Core.Case arm : match.cases()) {
            if (Core.withoutStanding(arm.body()) instanceof Core.Bool bool && !bool.value()) {
                continue;
            }
            if (only != null) {
                return null;
            }
            only = arm;
        }
        return only;
    }

    /** Which kind of rule one statement is. */
    private static Statement whatItStates(Core standing, InputReads reads, Symbols symbols,
                                          DeclarationNewtypes newtypes) {
        Core e = Core.withoutStanding(standing);
        if (e instanceof Core.Binary binary) {
            Comparison comparison = Comparison.of(binary).orElse(null);
            return comparison == null ? new Statement.NotRead(e, reads)
                    : new Statement.Compares(e, reads, comparison);
        }
        // A rule is read off a call the author wrote. What a pass composed — the size a comparison
        // means, a call written back out of a checked value — states nothing an author owes rows
        // for, so what is asked is which of those this is rather than whether a construct came back.
        if (e instanceof Core.PreservedCall call
                && call.application() instanceof ApplicationOrigin.Written) {
            StringPredicates.Stated states = StringPredicates.statedBy(call, symbols,
                    at -> reads.writtenStringOf(at, symbols, newtypes));
            if (states != null) {
                return new Statement.TellsStringsApart(call, reads, states);
            }
        }
        return new Statement.NotRead(e, reads);
    }
}
