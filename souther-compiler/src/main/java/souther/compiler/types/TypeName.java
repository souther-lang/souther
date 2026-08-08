package souther.compiler.types;

/**
 * A data type's identity: the module that declares it and the name written there. Two modules may
 * both declare {@code 金額}; those are different types, and only the pair tells them apart.
 *
 * <p>Every {@link Type.Ref} carries one of these, so a name that reached the checker has already
 * been resolved to its declaring module. What the source wrote — a bare {@code 金額}, a qualified
 * {@code probe.b.金額}, or an alias {@code B.金額} — is settled during resolution and does not
 * survive into the type.
 */
public record TypeName(String module, String name) implements Comparable<TypeName> {

    /** The module a primitive case name belongs to. {@code Int | DivisionByZero} unions a primitive
     * with a data case, so a primitive needs a name of this shape to sit in {@link Type.Union}; it
     * never reaches codegen as a class, since a primitive case maps to its boxed class by name. */
    public static final String PRIMITIVE = "souther";

    /** The module of the built-in error cases ({@code DivisionByZero}, {@code NotANumber}). It is
     * their real runtime package, so they need no special case when a class name is derived. */
    public static final String RUNTIME = "souther.runtime";

    public TypeName {
        if (module == null || name == null) {
            throw new IllegalArgumentException("module and name are required: " + module + "." + name);
        }
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
        for (Type.Prim prim : Type.Prim.values()) {
            if (prim.shown().equals(name())) {
                return prim;
            }
        }
        return null;
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

    /** The module of a name that denotes nothing. Not a real module, and no source may name it:
     * a name of this shape stands for a name the compiler could not resolve. */
    public static final String UNRESOLVED = "souther.unresolved";

    /** A name nothing denotes, keeping the spelling that was written so a later reader can quote it.
     * {@link TypeOps#denoted} turns it into {@link Type#ERRONEOUS}. */
    public static TypeName unresolved(String written) {
        return new TypeName(UNRESOLVED, written);
    }

    public boolean isUnresolved() {
        return module.equals(UNRESOLVED);
    }

    /** Another name declared in the same module — a sum's case, given the sum. */
    public TypeName sibling(String other) {
        return new TypeName(module, other);
    }

    public boolean isPrimitive() {
        return module.equals(PRIMITIVE);
    }

    /** The fully qualified form, {@code probe.b.金額}. Also the generated class's binary name. */
    public String qualified() {
        return module + "." + name;
    }

    @Override
    public int compareTo(TypeName other) {
        int byName = name.compareTo(other.name);
        return byName != 0 ? byName : module.compareTo(other.module);
    }

    @Override
    public String toString() {
        return qualified();
    }
}
