package souther.compiler.jvm;

/**
 * Entering a class this compilation emitted, from Java.
 *
 * <p>A caller says which generated class it wants and gets the class; what that class is called is
 * never in the caller's hands. This is ergonomics rather than a prohibition — a reader that genuinely
 * needs the name asks {@link SoutherJvmAbi#nameOf} and reads {@link JvmClassName#binaryName()} — but
 * it is what almost every reader wanted, and going through it means the name a reader is sent to is
 * the name that was emitted.
 */
public final class GeneratedClasses {

    private GeneratedClasses() {}

    /** The class {@code generated} was emitted as, loaded from {@code loader}. */
    public static Class<?> load(ClassLoader loader, GeneratedClass generated) throws ClassNotFoundException {
        return loader.loadClass(SoutherJvmAbi.nameOf(generated).binaryName());
    }
}
