package souther.compiler.check;

import souther.compiler.ast.Hir;

import java.util.ArrayList;
import java.util.List;

/**
 * The clauses a walk of a declaration and what it spreads found, and whether it found all of them.
 *
 * <p>Two things and not one, because a walk can come back with clauses and still be short. A
 * declaration spreads three types, one of which belongs to a module whose expansion could not be
 * worked out: what the other two state is true of every value of it and worth reading, and the rule
 * the third states was not read at all. A list alone says the first and loses the second, and a
 * reader with the list reports a value as held to exactly what it managed to read.
 *
 * <p>{@link #everyRuleReached} is what a reading turns into the widening it already has a word for.
 * It is not "the reading understood every clause" — a clause read to the end and found to be a shape
 * nothing takes apart is reached, and is that reading's own limit to report. It is the narrower
 * claim that nothing was left out before the reading began.
 */
public record ExpandedRules(List<TypeOps.Declared> reached, boolean everyRuleReached) {

    public ExpandedRules {
        reached = List.copyOf(reached);
    }

    /** The clauses alone, for a reader that has already accounted for what was not reached. */
    public List<Hir.InvariantClause> clauses() {
        List<Hir.InvariantClause> out = new ArrayList<>();
        for (TypeOps.Declared each : reached) {
            out.add(each.clause());
        }
        return List.copyOf(out);
    }

    /** These and {@code other}'s together, reaching everything only where both did. */
    ExpandedRules and(ExpandedRules other) {
        List<TypeOps.Declared> both = new ArrayList<>(reached);
        both.addAll(other.reached);
        return new ExpandedRules(both, everyRuleReached && other.everyRuleReached);
    }
}
