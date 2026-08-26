package souther.compiler.core;

import java.util.Collections;
import java.util.EnumMap;
import java.util.EnumSet;
import java.util.Map;
import java.util.Set;

/**
 * What the language declares of its kernels, as one value.
 *
 * <p>The half of a checked language snapshot that says what the standard library's operations take
 * and answer. Everything that emits a call to one reads it here: what a program carries across the
 * boundary and what the JVM backend derives its descriptors from are the same value, so there is no
 * arrangement under which two of them could be looking at different versions of the language.
 *
 * <p>A value rather than a registry to ask. Held as the library it came from, a reader could put any
 * question to it and would go on doing so; held as this, the only question is what a kernel was
 * declared with, which is the one an output has business asking.
 *
 * <p>Total over {@link Kernel}, and made so where one is built rather than checked again wherever
 * one is read. There is no partial snapshot to hold: a kernel this compiler names and the library
 * declares nothing for is refused at {@link #of}, which is the one place a snapshot comes from.
 */
public final class KernelSignatures {

    private final Map<Kernel, KernelSignature> declared;

    private KernelSignatures(Map<Kernel, KernelSignature> declared) {
        this.declared = declared;
    }

    /**
     * The snapshot of {@code declared}.
     *
     * @throws IllegalArgumentException where a kernel this compiler names is not among them. A
     *     reader asks with a kernel and is answered; there is no arm for a kernel the language has
     *     and this does not, so one arriving here would become a null somewhere far from the
     *     omission that made it.
     */
    public static KernelSignatures of(Map<Kernel, KernelSignature> declared) {
        Set<Kernel> missing = EnumSet.allOf(Kernel.class);
        missing.removeAll(declared.keySet());
        if (!missing.isEmpty()) {
            throw new IllegalArgumentException("this compiler names the kernel(s) "
                    + missing.stream().map(Kernel::key).toList()
                    + ", which the standard library declares nothing for");
        }
        return new KernelSignatures(
                Collections.unmodifiableMap(new EnumMap<>(declared)));
    }

    /** What {@code kernel} was declared to take and to answer. Never null: the language names a
     *  fixed set of kernels and a snapshot holding fewer cannot be made. */
    public KernelSignature signatureOf(Kernel kernel) {
        return declared.get(kernel);
    }
}
