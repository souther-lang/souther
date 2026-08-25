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
 * <p>One way a declaration enters, and it is the whole of the list. {@link #declared} — a
 * declaration world says one is at this address. Nearly always a module of this compilation wrote
 * it: the implicit unit data a module only names comes in this way too, because it is written into
 * the tree while the source is parsed, and so does a module read off the path, because its published
 * text is parsed like any other source. The standard library's own declarations come in the same
 * way, since which of the two declared it is its own question and
 * {@code Declarations.declaredByCompilation} is where it is asked.
 *
 * <p>There used to be a second, for what the language declares and no module does. It took a module
 * name and a spelling, and what it was for was that those declarations had no address to be found
 * at — so one was invented for them. They have one now, or they are a case of a closed set and are
 * not addressed at all ({@link TypeSymbol.OfLanguage}), and there is nothing left for it to do.
 *
 * <p>A name read back off a class the compiler is holding is not a third way. What a binary name
 * gives is an address, and a linker holding one asks the declaration world whether anything is
 * declared there — {@code Declarations.identify} and {@code Registry.identify} — rather than being
 * handed an identity for having spelled one. An identity that would be a declaration if one existed
 * is what {@code TypeName.UNRESOLVED} was, one level out.
 */
public final class TypeSymbols {

    private TypeSymbols() {
    }

    /**
     * The identity of a declaration a declaration world has said is at this address.
     *
     * <p>Asked where declarations are indexed, which is the one place that has the declaration and
     * the module that wrote it together, and by the two {@code identify} calls, which have just been
     * answered for the address by a registry or by the language's own vocabulary. A reader that pairs
     * a name with the module it happens to be compiling answers for a declaration here whatever the
     * name came from, which is why what may be handed to this is held from the source: a
     * declaration's own key, or an address something was found at.
     *
     * <p>Which of the two worlds declared it is a separate question and has its own answer
     * ({@code Declarations.declaredByCompilation}), because what a compilation may construct is
     * governed by {@code constructs} and the language's vocabulary is not.
     */
    public static TypeSymbol.AtModule declared(TypeKey key) {
        return new TypeSymbol.AtModule(key);
    }


}
