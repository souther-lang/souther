package souther.compiler.jvm;

import java.lang.constant.ClassDesc;

/**
 * The name a JVM class is spelled under: a binary name, and the descriptor and map key built from it.
 *
 * <p>Nothing outside this package can make one. The constructor is package-private and there is no
 * other way in, so the only route from a Souther entity to a JVM spelling is {@link
 * SoutherJvmAbi#nameOf}, and a reader that wants the class a declaration was emitted as has to name
 * the declaration rather than spell the class. That is the whole point of the type: a compiler that
 * restates the spelling somewhere else is not a compiler that fails a check, it is a compiler that
 * does not build.
 *
 * <p>A record would not hold this. The canonical constructor of a public record is public, so
 * {@code new JvmClassName("m.FooCase")} would be writable anywhere and the guarantee would be a
 * comment again.
 *
 * <p>The complete name is public — {@link #binaryName()} and {@link #classDesc()}. What is not public
 * is anything a caller could build a name back out of: no simple name, no package, no suffix. A
 * complete answer nobody restates is the shape that has held; a fragment every caller has to finish
 * is the shape that got restated at eleven sites.
 */
public final class JvmClassName {

    private final String binaryName;

    JvmClassName(String binaryName) {
        this.binaryName = binaryName;
    }

    /** The binary name, {@code m.FooCase} — what a class loader is asked for and what a diagnostic
     *  quotes. */
    public String binaryName() {
        return binaryName;
    }

    /** The same name as a descriptor, for the class file writer. */
    public ClassDesc classDesc() {
        return ClassDesc.of(binaryName);
    }

    /**
     * Where a class of this name is written, and read back: {@code demo/Foo.class}, relative to
     * whatever holds it — an output directory, a jar, a class path root.
     *
     * <p>A path is not an identity and the rule is the JVM's rather than this compiler's, which is
     * why it is a function of a name here rather than a kind of {@link GeneratedClass}. It is still a
     * rule with one place to live: written out at each of the four readers that wanted it, a compiler
     * that ever needs to write a class somewhere else has four places to look and no way to know it
     * found them all.
     */
    public static String classFile(String binaryName) {
        return binaryName.replace('.', '/') + ".class";
    }

    /** @see #classFile(String) */
    public String classFile() {
        return classFile(binaryName);
    }

    /** Whether {@code c} is the class of this name. The question a reader of a run asks — which is
     *  asked of the name the ABI decided, not of a spelling the reader assembled. */
    public boolean is(Class<?> c) {
        return c != null && c.getName().equals(binaryName);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof JvmClassName o && binaryName.equals(o.binaryName);
    }

    @Override
    public int hashCode() {
        return binaryName.hashCode();
    }

    @Override
    public String toString() {
        return binaryName;
    }
}
