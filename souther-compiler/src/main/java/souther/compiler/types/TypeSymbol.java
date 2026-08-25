package souther.compiler.types;

import souther.compiler.Reserved;

/**
 * A data type's identity: the module that declares it and the name written there. Two modules may
 * both declare {@code 金額}; those are different types, and only the pair tells them apart.
 *
 * <p>Every {@link Type.Ref} carries one of these, so a name that reached the checker has already
 * been resolved to its declaring module. What the source wrote — a bare {@code 金額}, a qualified
 * {@code probe.b.金額}, or an alias {@code B.金額} — is settled during resolution and does not
 * survive into the type.
 *
 * <p>The pair itself is {@link TypeKey}, which is what a class file carries and what a declaration
 * says of itself. This is that key where it stands for the declaration in the compiler's own
 * reasoning, and the two are told apart by more than which type a signature names: a key is
 * structural and anything holding two strings has one, while an identity comes from
 * {@link TypeSymbols} and nowhere else. {@link #key()} goes down to the address; nothing here comes
 * back up.
 */
public final class TypeSymbol implements Comparable<TypeSymbol> {

    /** The module a primitive case name belongs to. {@code Int | DivisionByZero} unions a primitive
     * with a data case, so a primitive needs a name of this shape to sit in {@link Type.Union}; it
     * never reaches codegen as a class, since a primitive case maps to its boxed class by name.
     *
     * <p>Not readable from outside. What a caller wants of it is {@link #isPrimitive()}, and a
     * caller that had the spelling wrote that question itself — which is the same question with
     * one more place to get it wrong. */
    private static final String PRIMITIVE = "souther";

    /** The module of the built-in error cases ({@code DivisionByZero}, {@code NotANumber}). It is
     * their real runtime package, so they need no special case when a class name is derived. */
    public static final String RUNTIME = "souther.runtime";

    private final TypeKey key;

    /**
     * Closed. An identity comes from {@link TypeSymbols}, which is the one edge from the structural
     * address to the identity the compiler reasons with; a caller that could build one from two
     * strings is a caller that could arrive at an identity without having been handed one.
     */
    TypeSymbol(String module, String name) {
        this.key = new TypeKey(module, name);
    }

    /** Which declaration this is, written down.
     *
     * <p>One direction only. Nothing here builds a name from a key: a key is what a class file
     * carries, and turning one back into the identity the compiler reasons with is the work of
     * whatever knows the declarations, which is not this. */
    public TypeKey key() {
        return key;
    }

    /** The module that declares it. */
    public String module() {
        return key.module();
    }

    /** The name written there. */
    public String name() {
        return key.name();
    }

    /** A primitive case name ({@code Int}) as it appears in a union. */
    public static TypeSymbol primitive(String name) {
        return TypeSymbols.ofLanguage(PRIMITIVE, name);
    }

    /** The same, minted from the primitive itself, which is where the spelling comes from. */
    public static TypeSymbol primitive(Type.Prim prim) {
        return TypeSymbols.ofLanguage(PRIMITIVE, prim.shown());
    }

    /**
     * The primitive this name denotes, or null where it names none.
     *
     * <p>The other direction of {@link #primitive(Type.Prim)}, and written as its inverse rather
     * than as a table beside it: a reader that needs the primitive back has one place to get it, and
     * a spelling can only be wrong here by being wrong in both directions at once. {@code Some} and
     * {@code None} are primitive-module names that denote no primitive, so they answer nothing.
     */
    public Type.Prim primitiveKind() {
        if (!isPrimitive()) {
            return null;
        }
        return Type.Prim.named(name());
    }

    /** A built-in error case ({@code DivisionByZero}). */
    public static TypeSymbol runtime(String name) {
        return TypeSymbols.ofLanguage(RUNTIME, name);
    }

    /** {@code Some} / {@code None}: written in a match arm over an {@code Option}, declared by no
     * module. They are named for the same reason a primitive case is — a name a pattern writes has to
     * denote something — and they name no class: an Option match dispatches on the runtime Option
     * classes, never on the arm's own name. */
    public static final TypeSymbol SOME = primitive("Some");

    /** @see #SOME */
    public static final TypeSymbol NONE = primitive("None");

    /** Option's case of that spelling, or {@code null} for any other. */
    public static TypeSymbol optionCase(String written) {
        return switch (written) {
            case "Some" -> SOME;
            case "None" -> NONE;
            default -> null;
        };
    }

    /** Whether this is a primitive case name — the {@code Int} of {@code Int | DivisionByZero}. */
    public boolean isPrimitive() {
        return module().equals(PRIMITIVE);
    }

    /**
     * Whether the language declares this rather than a module of some compilation.
     *
     * <p>The primitives, {@code Option}'s two cases and the prelude's runtime-backed data, together
     * and as one answer. Nothing publishes any of them — there is no {@code souther/$Module.class}
     * for a path to carry — so a reader that goes looking for the module behind one is asking after
     * an artifact that cannot exist, and the reader that did was told to add a dependency nobody
     * ships (#1049).
     *
     * <p>Read off the address and not off how the identity was minted. {@link TypeSymbols} has two
     * ways in, and which of them a given identity came through is not a fact about the declaration:
     * {@code Declarations.identify} answers for the language's own vocabulary through
     * {@link TypeSymbols#declared}, so one address would carry different origins by route. What is
     * asked here is what the declaration <em>is</em>, which its address settles, so two equal
     * identities answer alike.
     *
     * <p>{@link Reserved#isNamespace} is where that is written down, and this is the only place in
     * the compiler that reads it of a declaration. A caller holding an identity asks the identity.
     *
     * <p>Not the same question as which class carries it. {@code souther.runtime} is both the
     * namespace the prelude's data is addressed under and the package one backend ships it in, and
     * the readers that mean the second still spell {@link #RUNTIME} — that is #1038's inventory and
     * #1039's rule, and answering them through this would tidy the spelling away while leaving what
     * those two are about exactly where it is.
     */
    public boolean isDeclaredByLanguage() {
        return Reserved.isNamespace(module());
    }

    /** The fully qualified form, {@code probe.b.金額}. Also the generated class's binary name. */
    public String qualified() {
        return key.qualified();
    }

    @Override
    public int compareTo(TypeSymbol other) {
        return key.compareTo(other.key);
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof TypeSymbol other && key.equals(other.key);
    }

    @Override
    public int hashCode() {
        return key.hashCode();
    }

    @Override
    public String toString() {
        return qualified();
    }
}
