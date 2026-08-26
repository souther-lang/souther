package souther.compiler.examples;

import souther.compiler.core.Contract;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

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
 *
 * <p>A caller says what it has and not what follows from it. A row that wrote a value has the
 * answer; a row that wrote a bare case name has the case it is and nothing under it. Each is handed
 * over as it stands, and which rules the declaration decides from either is worked out where the
 * check was emitted.
 *
 * <p>A behavior is named by the module that declares it and not by the word a caller writes. A
 * {@code fake} may stand in for a dependency another module declares, and what such a value has to
 * keep is that module's clause, checked by the class that module emitted. So what is held here is
 * every reachable behavior's contract under the declaration it belongs to, and the module a check is
 * loaded from is the one on the behavior. Keyed by the spelling a row writes, a borrowed dependency
 * would be held to a namesake's clause or to none.
 */
final class EnsuresChecks {

    /** Every behavior a row or a fake here may state something about — this module's and the ones it
     *  borrows — under the declaration each is. */
    private final Map<ValueName.Behavior, Contract> contracts;

    private final ClassLoader loader;

    /**
     * The check of each behavior that has one, once it has been looked up.
     *
     * <p>Concurrent because one of these is the module's and a row is a thread. A row that overruns
     * its budget is abandoned rather than stopped — a pure computation reaches no interrupt point,
     * which is why every row is given a {@link FixtureReader} of its own — so a worker still inside
     * a check can be writing here while the next row's worker reads. Two workers looking one method
     * up is work done twice and nothing else; the map coming apart while they do is a failure that
     * would not reproduce.
     */
    private final Map<ValueName.Behavior, Method> found = new ConcurrentHashMap<>();

    /** The same for the check asked about a case. Kept apart from {@link #found} rather than under a
     *  spelled-together key: two questions, and a key that joined them would be a spelling to keep
     *  unique. */
    private final Map<ValueName.Behavior, Method> foundForCase = new ConcurrentHashMap<>();

    EnsuresChecks(ClassLoader loader, Map<ValueName.Behavior, Contract> contracts) {
        this.loader = loader;
        this.contracts = contracts;
    }

    /**
     * Whether {@code behavior} states anything of what it answers.
     *
     * <p>Asked of the contracts, which is where the answer is: a behavior writing no {@code ensures}
     * is not put in them ({@code Bodies.Contracts}), so being absent and stating nothing are one
     * fact rather than two that agree. Answerable without applying anything, because what a behavior
     * declares does not turn on an input — {@link #contractOf} reads the name and uses the arguments
     * only to check their number against it.
     */
    boolean states(ValueName.Behavior behavior) {
        return contracts.containsKey(behavior);
    }

    /**
     * What {@code behavior}'s check said of an answer of {@code answer} to {@code args}, or null
     * where every rule held — and where the behavior states nothing, which is every rule it has
     * holding.
     *
     * @throws IllegalStateException where the check could not be called, which is this compiler
     *                               failing to reach its own output rather than anything about the
     *                               values. Not a {@link FixtureException}: that says a written
     *                               fixture is at fault, and a caller catching one would report a
     *                               broken emission as an author's mistake
     */
    String notHeld(ValueName.Behavior behavior, Object[] args, Object answer) {
        Contract contract = contractOf(behavior, args);
        if (contract == null) {
            return null;
        }
        Object[] handed = Arrays.copyOf(args, args.length + 1);
        handed[args.length] = answer;
        return said(behavior.name(), () -> check(behavior, contract).invoke(null, handed));
    }

    /**
     * What {@code behavior}'s check said of an answer that is a {@code case} to {@code args}, or
     * null where every rule it decides held.
     *
     * <p>The case and no value, which is what a row writing a bare case name wrote. What is decided
     * from that is the declaration's own answer: the rules it leaves undecided are the ones that
     * read the answer, and they are held where the behavior answers, as everything nothing wrote a
     * value for is.
     *
     * @throws IllegalStateException on the same terms as {@link #notHeld}
     */
    String notHeldForCase(ValueName.Behavior behavior, Object[] args, TypeSymbol answered) {
        Contract contract = contractOf(behavior, args);
        if (contract == null) {
            return null;
        }
        Object[] handed = Arrays.copyOf(args, args.length + 1);
        handed[args.length] = SoutherJvmAbi.caseTokenOf(answered).qualified();
        return said(behavior.name(),
                () -> checkForCase(behavior, contract).invoke(null, handed));
    }

    /**
     * What {@code behavior} declares, where these arguments can be held to it; null where it
     * declares nothing.
     *
     * <p>Asked by the declaration, so a behavior another module declares is answered with that
     * module's clause. A behavior nothing here can name is absent, which is the same answer as one
     * that declares nothing — right here, because either way there is no clause for this value to be
     * held to and no class to load one from.
     */
    private Contract contractOf(ValueName.Behavior behavior, Object[] args) {
        Contract contract = contracts.get(behavior);
        if (contract == null) {
            return null;
        }
        if (args.length != contract.params().size()) {
            // Whoever built the arguments built them against the signature, so this is that reading
            // and this one disagreeing. Said rather than passed on to reflection, which would report
            // it as a method that is not there.
            throw new IllegalStateException("`" + behavior.name() + "` takes "
                    + contract.params().size() + " input(s) and the check was handed "
                    + args.length);
        }
        return contract;
    }

    /** An emitted check, called. */
    private interface Called {
        void call() throws ReflectiveOperationException;
    }

    /**
     * What {@code call} said, or null where it held.
     *
     * <p>One reading of an abort for both checks. Which entry point was called says what evidence
     * the declaration was asked from; what a violation of it is, and what an end other than a
     * violation means for the row, are the same either way.
     */
    private String said(String behavior, Called call) {
        try {
            call.call();
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
            // The class is emitted for every contract this answer holds, so a miss is that
            // correspondence broken rather than a behavior with nothing to check.
            throw new IllegalStateException("what `" + behavior
                    + "` declares could not be checked: " + e.getMessage(), e);
        }
    }

    /** {@code <module>.<behavior>$Ensures.check}, opened. */
    private Method check(ValueName.Behavior behavior, Contract contract)
            throws ReflectiveOperationException {
        return opened(found, behavior, "check", Object.class, contract);
    }

    /** {@code …$Ensures.checkCase}, opened. */
    private Method checkForCase(ValueName.Behavior behavior, Contract contract)
            throws ReflectiveOperationException {
        return opened(foundForCase, behavior, "checkCase", String.class, contract);
    }

    /**
     * One of the class's entry points, opened and remembered.
     *
     * <p>Every argument is a reference (ADR-0104), so what a descriptor is decided by is how many
     * parameters the behavior takes and what the last argument stands for — the answer, or the name
     * of the case it is. One place loads the class and spells the lookup, so the two entry points
     * cannot come to be reached in two ways.
     */
    private Method opened(Map<ValueName.Behavior, Method> cache, ValueName.Behavior behavior,
                          String name, Class<?> last, Contract contract)
            throws ReflectiveOperationException {
        Method known = cache.get(behavior);
        if (known != null) {
            return known;
        }
        // Loaded from the module that declares the behavior, which is where its check was emitted.
        Class<?> c = GeneratedClasses.load(loader, new GeneratedClass.Ensures(
                new GeneratedClass.BehaviorInterface(behavior.module(), behavior.name())));
        Class<?>[] params = new Class<?>[contract.params().size() + 1];
        Arrays.fill(params, Object.class);
        params[contract.params().size()] = last;
        Method found = c.getDeclaredMethod(name, params);
        found.setAccessible(true);
        cache.put(behavior, found);
        return found;
    }
}
