package souther.compiler.ast;

import souther.compiler.types.TypeSymbol;

/**
 * Where a construction standing in a body came from — what a permission check needs in order to tell
 * a construction the body makes from one that arrived in it already made.
 *
 * <p>Expansion is why the question has to be answered at all. A value is substituted at each
 * reference and a published body is spliced into its reader, so a construction written somewhere
 * else ends up as the same node one written here would be. Asking the node is the only way left.
 *
 * <p>The two ways in are held apart because they are not answered alike. A published body names the
 * module that published it, and that module hands over only what it declares: a construction of a
 * third module's type is nobody's to hand over, so the module is compared against the type's. A
 * value reference names no module — the construction belongs to the definition of the value, and the
 * behavior reading the name originates nothing whatever module declared the type.
 *
 * <p>This is not a value a pass names. Its arms are declared in this package and nothing outside can
 * name one, so the only origins there are, are the ones the two forms that hold one make: a
 * construction is its own where it is built, and becomes one of the other two where a body crosses
 * into a reader. What a pass elsewhere can do with an origin is hand the one it was given back —
 * {@link Hir.NewData} and {@link Hir.Apply} take none when they are built, and carry the one they
 * have when they are rebuilt.
 *
 * <p>The transitions, of which carried by a value is the last word:
 *
 * <pre>
 * Own          --published(m)--&gt; Published(m)     --byValue--&gt; ByValue
 * Published(_) --published(m)--&gt; Published(m)     --byValue--&gt; ByValue
 * ByValue      --published(_)--&gt; ByValue          --byValue--&gt; ByValue
 * </pre>
 *
 * <p>A construction a value carried stays the value's however many published bodies then carry it:
 * the definition of the value is where it was made, and a reader further along is no more the one
 * that made it than the first was. Answering {@code Published} there would put a construction back
 * under the authority of a body that only passed it on.
 */
public sealed interface ConstructionOrigin
        permits Origins.Own, Origins.Published, Origins.ByValue {

    /**
     * Whether the body holding this construction of {@code built} was handed it rather than making
     * it, and so answers for none of it.
     */
    default boolean carried(TypeSymbol.AtModule built) {
        return switch (this) {
            case Origins.Own _ -> false;
            case Origins.Published published -> published.module().equals(built.module());
            case Origins.ByValue _ -> true;
        };
    }

    /** Whether a value this body named is what carried the construction in. */
    default boolean viaValueReference() {
        return this instanceof Origins.ByValue;
    }

    /** The same construction, carried into a reader by {@code module}'s published body. */
    default ConstructionOrigin publishedIn(String module) {
        return this instanceof Origins.ByValue ? this : new Origins.Published(module);
    }

    /** The same construction, carried into a body by a value that body named. */
    default ConstructionOrigin carriedByValue() {
        return Origins.ByValue.IT_IS;
    }
}
