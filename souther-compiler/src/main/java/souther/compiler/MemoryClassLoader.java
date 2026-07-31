package souther.compiler;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Supplier;

/**
 * Loads freshly generated classes from an in-memory binary-name → bytecode map, delegating anything
 * unknown to the parent loader. Used to run generated code without writing {@code .class} files:
 * the compiler's compile-time {@code $Ctfe.check} evaluation and {@link Runner}'s behavior driving.
 *
 * <p>Registered parallel-capable, because a module's example rows are evaluated at the same time and
 * loading a class is most of what they do. A loader that is not registered locks on itself for every
 * name, so the rows would queue for the one thing they all have to do; registered, each name has its
 * own lock and two rows loading different classes never meet.
 */
public final class MemoryClassLoader extends ClassLoader {

    static {
        registerAsParallelCapable();
    }

    private final Map<String, byte[]> classes;
    /** Classes defined on the fly (a multi-argument fake's base subclass; issue #57), cached so a name
     * is never defined twice — which would be a {@code LinkageError}. */
    private final Map<String, Class<?>> defined = new ConcurrentHashMap<>();

    public MemoryClassLoader(Map<String, byte[]> classes, ClassLoader parent) {
        super(parent);
        this.classes = classes;
    }

    @Override
    protected Class<?> findClass(String name) throws ClassNotFoundException {
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
     * <p>Guarded by the same per-name lock the JVM takes to load that name, rather than by this
     * loader: holding the loader while defining would put every name behind one lock again, which is
     * what registering parallel-capable is for. */
    Class<?> define(String name, Supplier<byte[]> bytes) {
        Class<?> known = defined.get(name);
        if (known != null) {
            return known;
        }
        synchronized (getClassLoadingLock(name)) {
            return defined.computeIfAbsent(name, n -> {
                byte[] b = bytes.get();
                return defineClass(n, b, 0, b.length);
            });
        }
    }
}
