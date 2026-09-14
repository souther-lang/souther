package souther.compiler.check;

import souther.compiler.types.TypeKey;

/**
 * Where a reading gets a declaration's clauses in the representation it reads
 * ({@link ExpandedClauses}).
 *
 * <p>One question and one input: which declaration. Who is asking is not an input and cannot be
 * one, which is the whole of what this interface is for — a reading that could say which module was
 * asking is a reading whose answer could differ between two of them, and that is what
 * spec §invariant-discharge-representation forbids: where a declaration was written does not decide
 * what can be discharged against it.
 *
 * <p>Nothing else goes in here. No module, no representation to choose, no declaration node to fall
 * back on: a second input is a second answer, and the caller that supplied it would be the one
 * deciding which.
 */
@FunctionalInterface
public interface ExpandedClauseLookup {

    /** What is known about {@code declaration}'s clauses. */
    ExpandedClauseResult of(TypeKey declaration);

    /** Nothing declared anywhere — for a reading over primitives, which asks of no declaration. */
    ExpandedClauseLookup NONE = ExpandedClauseResult.NotDeclared::new;
}
