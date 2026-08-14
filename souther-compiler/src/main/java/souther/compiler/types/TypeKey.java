package souther.compiler.types;

/**
 * Which declaration, written down: the module that declares it and the name written there.
 *
 * <p>Structural, and public for that reason. A key written into a class file and read back has to
 * compare equal to the one the compiler holds, which is what makes it the identity that survives a
 * compilation — the same declaration, named the same way, in the next one.
 *
 * <p>Not what a name means. Two modules may both declare {@code 金額}, and the pair tells those
 * apart; what neither the pair nor anything else here says is whether a declaration of that key
 * exists, whether the module asking may reach it, or what it is a declaration of. Those are
 * {@code TypeScope} and {@code Declarations}, and nothing turns a key into one of their answers —
 * a key is what you have when you have read a name off a class file, and looking it up is a
 * question for whatever knows the declarations.
 */
public record TypeKey(String module, String name) implements Comparable<TypeKey> {

    public TypeKey {
        if (module == null || name == null) {
            throw new IllegalArgumentException(
                    "module and name are required: " + module + "." + name);
        }
    }

    /** The fully qualified form, {@code probe.b.金額}. Also the generated class's binary name. */
    public String qualified() {
        return module + "." + name;
    }

    @Override
    public int compareTo(TypeKey other) {
        int byName = name.compareTo(other.name);
        return byName != 0 ? byName : module.compareTo(other.module);
    }

    @Override
    public String toString() {
        return qualified();
    }
}
