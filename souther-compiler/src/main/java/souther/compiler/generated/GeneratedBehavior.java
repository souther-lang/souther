package souther.compiler.generated;

import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.SoutherJvmAbi;

/**
 * A behavior this compilation emitted, entered from Java.
 *
 * <p>Entering one means knowing that it has a no-argument constructor, that the method is called
 * {@code apply}, and that its parameters are erased to {@code Object} — codegen's decisions, written
 * out below because a caller has to act on them somewhere. This is that somewhere, and the only one:
 * the ABI has a producer and it has a consumer, and each is one place.
 *
 * <p>The class name is not written out, because it cannot be. A caller names the behavior and
 * {@link SoutherJvmAbi} says what its implementation is called; there is no way from here to a
 * spelling that is not that one. Restating it is what happened before, and how the CLI and the
 * compiler came to spell one name two ways.
 */
public final class GeneratedBehavior {

    private GeneratedBehavior() {}

    /**
     * The behavior applied to its arguments.
     *
     * <p>The two ways this can fail are two different things and are left told apart. The behavior
     * itself throwing arrives as an {@code InvocationTargetException} and is the behavior's failure.
     * Anything else — the class not there, no no-arg constructor, no reachable {@code apply} — is
     * this being unable to start it, which after the exposed check is codegen and the caller
     * disagreeing rather than anything the module did. Reported as one, the second reads as the
     * behavior having run and failed, and sends the author looking through a body that was never
     * entered — so both are thrown as they arrived and the caller catches the narrower one first.
     */
    public static Object apply(ClassLoader loader, String pkg, String behavior, Object[] args)
            throws ReflectiveOperationException {
        Class<?> c = GeneratedClasses.load(loader, new GeneratedClass.BehaviorImpl(pkg, behavior));
        Object instance = c.getConstructor().newInstance();
        Class<?>[] paramTypes = new Class<?>[args.length];
        java.util.Arrays.fill(paramTypes, Object.class);
        return c.getMethod("apply", paramTypes).invoke(instance, args);
    }

    /** Where a compiled behavior is entered, for a caller that has to say the name rather than use
     *  it — a report that the class was not there. The ABI decides it and is asked. */
    public static String implClass(String pkg, String behavior) {
        return SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorImpl(pkg, behavior)).binaryName();
    }
}
