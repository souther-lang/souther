package souther.compiler.types;

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
 * reasoning, and it is still built from two strings by anything that has two strings — which is
 * what makes it an identity a reader can assemble rather than one it was handed. Closing that is
 * the work {@code TypeSymbol} is for; until then, what a key is and what an identity is are told
 * apart by which of the two types a signature names.
 */
public final class TypeName implements Comparable<TypeName> {

    /** The module a primitive case name belongs to. {@code Int | DivisionByZero} unions a primitive
     * with a data case, so a primitive needs a name of this shape to sit in {@link Type.Union}; it
     * never reaches codegen as a class, since a primitive case maps to its boxed class by name. */
    public static final String PRIMITIVE = "souther";

    /** The module of the built-in error cases ({@code DivisionByZero}, {@code NotANumber}). It is
     * their real runtime package, so they need no special case when a class name is derived. */
    public static final String RUNTIME = "souther.runtime";

    private final TypeKey key;

    public TypeName(String module, String name) {
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
    public static TypeName primitive(String name) {
        return new TypeName(PRIMITIVE, name);
    }

    /** The same, minted from the primitive itself, which is where the spelling comes from. */
    public static TypeName primitive(Type.Prim prim) {
        return new TypeName(PRIMITIVE, prim.shown());
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
    public static TypeName runtime(String name) {
        return new TypeName(RUNTIME, name);
    }

    /** {@code Some} / {@code None}: written in a match arm over an {@code Option}, declared by no
     * module. They are named for the same reason a primitive case is — a name a pattern writes has to
     * denote something — and they name no class: an Option match dispatches on the runtime Option
     * classes, never on the arm's own name. */
    public static final TypeName SOME = primitive("Some");

    /** @see #SOME */
    public static final TypeName NONE = primitive("None");

    /** Option's case of that spelling, or {@code null} for any other. */
    public static TypeName optionCase(String written) {
        return switch (written) {
            case "Some" -> SOME;
            case "None" -> NONE;
            default -> null;
        };
    }

    /** Another name declared in the same module — a sum's case, given the sum. */
    public TypeName sibling(String other) {
        return new TypeName(module(), other);
    }

    public boolean isPrimitive() {
        return module().equals(PRIMITIVE);
    }

    /** The fully qualified form, {@code probe.b.金額}. Also the generated class's binary name. */
    public String qualified() {
        return key.qualified();
    }

    @Override
    public int compareTo(TypeName other) {
        return key.compareTo(other.key);
    }

    @Override
    public boolean equals(Object o) {
        return o instanceof TypeName other && key.equals(other.key);
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
