package souther.compiler.check;

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

    /** A built-in error case ({@code DivisionByZero}). */
    public static TypeName runtime(String name) {
        return new TypeName(RUNTIME, name);
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
