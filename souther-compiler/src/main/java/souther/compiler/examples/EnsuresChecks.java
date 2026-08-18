package souther.compiler.examples;

import souther.compiler.check.BehaviorContract;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * The emitted check, run over values a row or a fake's table states.
 *
 * <p>A fixture's operands are compiled and run as the module's own code, so what a row writes exists
 * in this loader as a live value — which is everything the check needs. So the clause is not read
 * here and interpreted: the same {@code $Ensures.check} that runs where the behavior answers is
 * invoked over the row's values, and what it says is what the row is told. A second reader of a
 * clause would be a second answer to what a clause means, and the two would come apart.
 *
 * <p>Whether there is a check to run is asked of the contracts, not of the loader. A class that will
 * not load is a compile that did not emit what it said it would, and taking that for "the behavior
 * declares nothing" would report a broken emission as a model with nothing to say.
 *
 * <p>The one place a check is invoked from a fixture: loading the class, spelling the call, and
 * unwrapping what reflection wraps are the same three steps wherever a stated value is held, and
 * writing them twice is two answers to how a check is called.
 */
final class EnsuresChecks {

    /** The behaviors of the module being evaluated that state something, under the name a row and a
     *  fake write. */
    private final Map<String, BehaviorContract> contracts;

    private final String module;
    private final ClassLoader loader;

    /** The check of each behavior that has one, once it has been looked up. */
    private final Map<String, Method> found = new HashMap<>();

    EnsuresChecks(String module, ClassLoader loader, Map<String, BehaviorContract> contracts) {
        this.module = module;
        this.loader = loader;
        this.contracts = contracts;
    }

    /** Whether {@code behavior} states anything about what it answers. */
    boolean states(String behavior) {
        return contracts.containsKey(behavior);
    }

    /**
     * What {@code behavior}'s check said of an answer of {@code answer} to {@code args}, or null
     * where every rule held — and where the behavior states nothing, which is every rule it has
     * holding.
     *
     * @throws FixtureException where the check could not be reached, which is this compiler failing
     *                          to call its own output rather than anything about the values
     */
    String notHeld(String behavior, Object[] args, Object answer) {
        BehaviorContract contract = contracts.get(behavior);
        if (contract == null) {
            return null;
        }
        if (args.length != contract.params().size()) {
            // Whoever built the arguments built them against the signature, so this is that reading
            // and this one disagreeing. Said rather than passed on to reflection, which would report
            // it as a method that is not there.
            throw new FixtureException("`" + behavior + "` takes " + contract.params().size()
                    + " input(s) and the check was handed " + args.length);
        }
        Object[] handed = Arrays.copyOf(args, args.length + 1);
        handed[args.length] = answer;
        try {
            check(behavior, contract).invoke(null, handed);
            return null;
        } catch (InvocationTargetException ite) {
            Throwable cause = ite.getCause();
            // Matched by name: the check runs under the loader the classes are in, and the runtime
            // it aborts with is whatever that loader reads it from. What is wanted here is only
            // which abort it was — the same reading a row's own application does.
            if (cause != null
                    && "souther.runtime.ConstraintViolation".equals(cause.getClass().getName())) {
                return cause.getMessage();
            }
            // Not the clause failing: the model's code ran and ended some other way, and what that
            // means for the row — a budget spent, a stack run out — is read where the row is.
            switch (cause) {
                case null -> throw new IllegalStateException("a check threw nothing", ite);
                case RuntimeException re -> throw re;
                case Error err -> throw err;
                default -> throw new IllegalStateException(
                        "a check threw a checked exception: " + cause, cause);
            }
        } catch (ReflectiveOperationException e) {
            throw new FixtureException(
                    "what `" + behavior + "` declares could not be checked: " + e.getMessage());
        }
    }

    /** {@code <module>.<behavior>$Ensures.check}, opened. Every argument is a reference (ADR-0104),
     *  so the descriptor is decided by how many parameters the behavior takes and nothing else. */
    private Method check(String behavior, BehaviorContract contract)
            throws ReflectiveOperationException {
        Method known = found.get(behavior);
        if (known != null) {
            return known;
        }
        Class<?> c = GeneratedClasses.load(loader,
                new GeneratedClass.Ensures(new GeneratedClass.BehaviorInterface(module, behavior)));
        Class<?>[] params = new Class<?>[contract.params().size() + 1];
        Arrays.fill(params, Object.class);
        Method check = c.getDeclaredMethod("check", params);
        check.setAccessible(true);
        found.put(behavior, check);
        return check;
    }
}
