package souther.compiler.generated;

import java.util.Map;
import java.util.function.Supplier;

/**
 * Loads freshly generated classes from an in-memory binary-name → bytecode map, delegating anything
 * unknown to the parent loader. Used to run generated code without writing {@code .class} files:
 * the compiler's compile-time {@code $Ctfe.check} evaluation, the rows an {@code example} states,
 * and the behavior {@code souther run} drives. None of the three is the reason it exists — it is
 * how a compilation's classes become classes at all.
 */
public final class MemoryClassLoader extends ClassLoader {

    private final Map<String, byte[]> classes;
    /** Classes defined on the fly (a multi-argument fake's base subclass; issue #57), cached so a name
     * is never defined twice — which would be a {@code LinkageError}. */
    private final Map<String, Class<?>> defined = new java.util.concurrent.ConcurrentHashMap<>();

    public MemoryClassLoader(Map<String, byte[]> classes, ClassLoader parent) {
        super(parent);
        this.classes = classes;
    }

    /**
     * A name this loader holds is loaded from what this loader holds, and every other name is left
     * to the parent.
     *
     * <p>The default order is the other way round, and that is wrong here. A compile's classes sit
     * over a module path, and the point of putting them there is that a module being compiled is the
     * one that runs; delegating first hands the name to the path, so a class file left from an
     * earlier build answers instead. What ran was then the old code — an example was compared against
     * an implementation this compile did not produce, and a correct model was reported as one whose
     * example does not hold. It also runs code this compile did not generate, which is code with none
     * of the counting in it, so the budget that is supposed to bound an evaluation is not there.
     *
     * <p>Only for names this loader holds. Everything else — the JDK, the runtime, the compiler's own
     * classes that generated code calls into — is the parent's, and taking those away from it would
     * define a second copy of a class the caller already has.
     */
    @Override
    protected Class<?> loadClass(String name, boolean resolve) throws ClassNotFoundException {
        synchronized (getClassLoadingLock(name)) {
            Class<?> already = findLoadedClass(name);
            if (already == null && (classes.containsKey(name) || defined.containsKey(name))) {
                already = findClass(name);
            }
            if (already == null) {
                return super.loadClass(name, resolve);
            }
            if (resolve) {
                resolveClass(already);
            }
            return already;
        }
    }

    @Override
    protected Class<?> findClass(String name) throws ClassNotFoundException {
        Class<?> onTheFly = defined.get(name);
        if (onTheFly != null) {
            return onTheFly;
        }
        byte[] b = classes.get(name);
        if (b == null) {
            throw new ClassNotFoundException(name);
        }
        return defineClass(name, b, 0, b.length);
    }

    /** Defines {@code name} once, generating the bytes lazily only on the first (cache-miss) call — a
     * second call with the same name returns the already-defined class without rebuilding the bytecode
     * (the bytes are identical; the fake body is injected at construction, not baked into the class).
     *
     * <p>Public for the caller that needs it: a multi-argument fake's base subclass is built while an
     * {@code example} runs, which is in another package. Everything this package publishes is public
     * for that kind of reason and none of it is a supported API (see {@code package-info}). */
    public Class<?> define(String name, Supplier<byte[]> bytes) {
        return defined.computeIfAbsent(name, n -> {
            byte[] b = bytes.get();
            return defineClass(n, b, 0, b.length);
        });
    }
}
