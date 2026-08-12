package souther.compiler.generated;

import souther.compiler.codegen.Backend;

/**
 * A behavior this compilation emitted, entered from Java.
 *
 * <p>Entering one means knowing that it has a no-argument constructor, that the method is called
 * {@code apply}, and that its parameters are erased to {@code Object} — codegen's decisions, written
 * out below because a caller has to act on them somewhere. This is that somewhere, and the only one:
 * the ABI has a producer and it has a consumer, and each is one place.
 *
 * <p>The class name is not written out, because it does not have to be. {@link Backend} decides it
 * and is asked, which is what the two of them being one rule looks like. Restating it here is exactly
 * what happened before and how the CLI and the compiler came to spell one name two ways.
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
        Class<?> c = loader.loadClass(implClass(pkg, behavior));
        Object instance = c.getConstructor().newInstance();
        Class<?>[] paramTypes = new Class<?>[args.length];
        java.util.Arrays.fill(paramTypes, Object.class);
        return c.getMethod("apply", paramTypes).invoke(instance, args);
    }

    /** Where a compiled behavior is entered. Codegen decides that name and is asked for it — the
     *  rule was written there once, and a second statement of a name is a second name. */
    public static String implClass(String pkg, String behavior) {
        return pkg + "." + Backend.behaviorImplClass(behavior);
    }
}
