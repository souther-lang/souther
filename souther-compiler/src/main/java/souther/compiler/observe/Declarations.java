package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

/**
 * What the declarations of an accepted program are made of, asked of the world that holds them.
 *
 * <p>One world, total over what it should hold. This compile holds what its check settled and a
 * snapshot holds what it publishes, and each is asked by the declaration's own identity — a data
 * names the module that wrote it, so there is no order in which one module's declarations are tried
 * before another's and two data of one name cannot be confused for one another.
 *
 * <p>Total, or a refusal. A declaration this world should hold and does not is not answered: read
 * as a declaration with nothing under it, a value of it would be compared as whatever its parts
 * happen to look like — which is the one thing a row may not come to mean. Each world refuses in
 * the one place it knows its own membership, and no reader of one has to decide what an absence
 * meant.
 *
 * <p>Not the reading an editor makes. A text that has not checked has declarations that denote
 * nothing yet, and there is nothing there to refuse; what that world answers is
 * {@link FieldTypes} of its own.
 */
public interface Declarations {

    /**
     * What a value of {@code declared} is made of.
     *
     * @throws IllegalStateException where this world should hold {@code declared} and does not
     */
    Composed of(TypeSymbol.AtModule declared);
}
