package souther.compiler.check;

/**
 * A relation known of every element of a container, to be read again at the element a combinator's
 * closure is handed: a predicate stated of the elements ({@link Quantified}), or a bound the
 * operation that listed them keeps them to ({@link ElementBound}).
 */
sealed interface ElementRelation permits Quantified, ElementBound {}
