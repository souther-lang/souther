package souther.compiler.check;

import souther.compiler.types.TypeSymbol;

import java.util.function.Predicate;

/**
 * Which rules a reading was asked to leave out.
 *
 * <p>A reading is asked to leave a declaration's rules out so that the end which moves says which
 * declaration was holding it. What is left out is a property of each rule — the declaration that
 * wrote it — and not of the value the reading happens to be opened at. The two are the same name
 * only where a declaration writes its own clauses and spreads nothing: a rule a spread carries in
 * was written where it was written, and a sum states what its cases share while writing none of it.
 *
 * <p><b>A type and not a predicate.</b> Held as a {@code Predicate}, a caller could hand one over
 * a position's name and it would compile — a method reference to {@code equals} takes an
 * {@code Object} and satisfies a predicate of any argument — and the reading would leave nothing
 * out while looking as though it had. Nothing here can be built except by naming declarations, and
 * nothing outside asks the question in any other terms.
 *
 * @param declarations which declarations' rules are left out, named as a caller thinks of them
 */
record RulesLeftOut(Predicate<TypeSymbol> declarations) {

    /** Every rule is read. */
    static final RulesLeftOut NONE = new RulesLeftOut(_ -> false);

    /** The rules {@code these} names wrote, wherever they are read. */
    static RulesLeftOut writtenOn(Predicate<TypeSymbol> these) {
        return new RulesLeftOut(these);
    }

    /** Whether this reading was asked to leave {@code rule} out. Asked of the rule, which carries
     *  the declaration it was written on however far it has travelled. */
    boolean excludes(RuleRef.Invariant rule) {
        return declarations.test(rule.clause().id().declaredOn());
    }
}
