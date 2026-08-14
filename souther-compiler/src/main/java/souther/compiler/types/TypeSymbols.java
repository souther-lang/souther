package souther.compiler.types;

/**
 * Where a declaration identity comes into existence.
 *
 * <p>An identity is not something a reader assembles from two strings. It exists because something
 * put a declaration into the world this compilation reasons about, and this is the edge that says
 * so: {@link TypeKey} goes in — the structural address a class file carries and a query is asked
 * with — and a {@link TypeSymbol} comes out, which is the identity the compiler reasons with.
 *
 * <p>One direction, and it is here. {@link TypeSymbol#key()} goes the other way and is public, because
 * a caller holding an identity was handed one already; what is closed is arriving at an identity
 * without having been. That is what made a spelling and an identity interchangeable, which is what
 * issues #464, #696 and #700 each were.
 *
 * <p>Three ways a declaration enters, and they are the whole of the list:
 *
 * <ul>
 *   <li>{@link #declared} — a module of this compilation wrote it. The implicit unit data a module
 *       only names comes in this way too: it is written into the tree while the source is parsed,
 *       so by the time declarations are indexed it is one of them. A module read off the path
 *       comes in this way as well, because its published text is parsed like any other source.</li>
 *   <li>{@link #ofLanguage} — the language declares it and no module does: a primitive standing in a
 *       union, {@code Option}'s two cases, the prelude's runtime-backed data.</li>
 *   <li>{@link #recovered} — a class the compiler is holding says which declaration it is. The one
 *       caller reads a binary name off a live value, and what it gets is a candidate: whether
 *       anything declares it is the declaration world's to answer, and this says nothing about
 *       it.</li>
 * </ul>
 */
public final class TypeSymbols {

    private TypeSymbols() {
    }

    /**
     * The identity of a declaration a module of this compilation wrote.
     *
     * <p>Asked where declarations are indexed, which is the one place that has the declaration and
     * the module that wrote it together. A reader that pairs a name with the module it happens to
     * be compiling answers for a declaration here whatever the name came from.
     */
    public static TypeSymbol declared(TypeKey key) {
        return new TypeSymbol(key.module(), key.name());
    }

    /**
     * The identity of something the language declares rather than a module: a primitive case name,
     * {@code Option}'s cases, the prelude's runtime-backed data.
     *
     * <p>Its own way in because it is its own kind of fact. Nothing indexes these — there is no
     * source that declares {@code Int} — and a compilation that declares nothing at all still has
     * them.
     */
    static TypeSymbol ofLanguage(String module, String name) {
        return new TypeSymbol(module, name);
    }

    /**
     * A candidate identity read off a name a class carries.
     *
     * <p>What comes back is an address the caller has yet to ask about. The linker reads one off a
     * binary name to find out which declaration a live value is of, and the answer is only a
     * declaration once the declaration world has said it has one — which is why this is separate
     * from {@link #declared}, and why nothing here is registered by asking.
     */
    public static TypeSymbol recovered(TypeKey key) {
        return new TypeSymbol(key.module(), key.name());
    }
}
