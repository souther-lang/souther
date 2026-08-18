package souther.compiler.examples;

import souther.compiler.check.Sig;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.meta.ClassFileDeclarations;
import souther.compiler.meta.PublishedClasses;
import souther.compiler.observe.Applied;

import java.io.IOException;
import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * An answerer for one behavior an implementation was supplied for, and this compile's own for the
 * rest.
 *
 * <p>A module declares behaviors of both kinds, so the resolution is per behavior and not per run:
 * a row of a behavior with a {@code let} body is applied as the class this compile emitted while a
 * row of the injected one it sits beside is applied as the supplied instance, in one evaluation.
 * Delegating rather than replacing is what makes that true without either side knowing about the
 * other.
 *
 * <p>Two things are worked out from the instance, and both by asking whatever already decides them.
 *
 * <p><em>Which behavior it is for.</em> The base it extends is of another build and another loader,
 * so no class identity is comparable and {@code instanceof} against anything this compile emitted
 * answers no. What is comparable is the binary name, and
 * {@link SoutherJvmAbi#nameOf(GeneratedClass)} is the one place the emitter's naming lives. Taking
 * {@code FindTodoImpl} apart into {@code findTodo} would restate that rule, and a restated rule goes
 * on answering after the original moves — binding a row of a behavior nothing supplied.
 *
 * <p><em>Which declarations it reads values by.</em> Its own loader's, read as bytes:
 * {@link ClassFileDeclarations} over that loader's class resources. The annotations are
 * {@code CLASS} retention, so this is a read of class files and not of reflection. Nothing is asked
 * of the caller for either, which is what makes it impossible to state either wrongly.
 */
final class BoundImplementation implements Answerer {

    private final Object implementation;
    private final Map<String, Sig> sigs;
    private final Answerer generatedHere;
    private final String module;

    /** The binary names of everything the instance is, so asking whether it is a behavior's base is
     *  a lookup rather than a walk per behavior. */
    private final Set<String> is;

    /** What the instance's own build declared, read from the loader that has its classes. */
    private final PublishedClasses theirs;

    /** The instance's values, read into its classes. */
    private final Crossing crossing;

    BoundImplementation(Object implementation, Map<String, Sig> sigs, Answerer generatedHere,
                        String module) {
        this.implementation = implementation;
        this.sigs = sigs;
        this.generatedHere = generatedHere;
        this.module = module;
        this.is = everythingItIs(implementation.getClass());
        ClassLoader loader = implementation.getClass().getClassLoader();
        this.theirs = new ClassFileDeclarations(binaryName -> bytesOf(loader, binaryName));
        this.crossing = new Crossing(loader);
    }

    /**
     * The supplied instance where it is the behavior's, and this compile's answer everywhere else.
     *
     * <p>Asked of the ABI and not of the module: a behavior this compile also generated an
     * implementation for is still answered by the instance if the instance is one of its bases, and
     * that is what an implementation supplied for it means. A behavior it is not a base of never
     * reaches the crossing at all.
     */
    @Override
    public Answer of(String behavior) {
        if (!is.contains(baseOf(behavior))) {
            return generatedHere.of(behavior);
        }
        Sig sig = sigs.get(behavior);
        if (sig == null) {
            throw new IllegalStateException("`" + behavior + "` is a base of the bound"
                    + " implementation and has no signature in the module the rows are written for");
        }
        return new Answer.Something() {

            @Override
            public Origin origin() {
                return new Origin.Published(theirs);
            }

            @Override
            public Applying applying(List<DependencyStandin> standins) {
                if (!standins.isEmpty()) {
                    // An injected behavior has no requirements, so nothing stands in for one. A
                    // stand-in reaching here would have to be made into an instance of this build's
                    // classes, which is a value boundary nothing has designed.
                    throw new IllegalStateException("`" + behavior + "` was supplied an"
                            + " implementation and has " + standins.size() + " requirement(s)");
                }
                return BoundImplementation.this.applying(behavior, sig);
            }
        };
    }

    private Applying applying(String behavior, Sig sig) {
        return new Applying() {

            @Override
            public Applied applied() {
                return new Applied.Bound();
            }

            @Override
            public Object to(List<Handed> arguments) {
                return apply(behavior, sig, arguments);
            }
        };
    }

    /**
     * The instance applied to the row's arguments, each read into its own build's classes.
     *
     * <p>What comes back needs nothing done to it: an answer is read by the name its class carries
     * and the accessor every data has, neither of which is a class identity.
     */
    private Object apply(String behavior, Sig sig, List<Handed> arguments) {
        if (arguments.size() != sig.ins().size()) {
            throw new IllegalStateException("`" + behavior + "` takes " + sig.ins().size()
                    + " and the row handed over " + arguments.size());
        }
        Object[] args = new Object[arguments.size()];
        for (int i = 0; i < args.length; i++) {
            args[i] = crossing.crossed(sig.ins().get(i), arguments.get(i).neutral().read());
        }
        Method apply = applyOf(args.length);
        try {
            return apply.invoke(implementation, args);
        } catch (InvocationTargetException ite) {
            // What the supplied code came back with, carried out as it stands. Whose failure it is
            // and what it means for the row are read where the row is — which is the same reading a
            // row of a `let` body gets, and is why the two arrive the same way.
            throw new InvocationFailure(ite.getCause());
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
        }
    }

    /**
     * The {@code apply} the instance supplies, of the arity the behavior declares.
     *
     * <p>A bridge is passed over. A single-input behavior's base is a {@code Behavior<In,Out>}, so a
     * Java implementation of it carries both its own typed {@code apply} and the erased bridge that
     * dispatches to it; invoking the bridge would work, and taking whichever came first would make
     * which one runs depend on a reflection order nothing states.
     */
    private Method applyOf(int arity) {
        Method found = null;
        for (Method m : implementation.getClass().getMethods()) {
            if (m.getName().equals("apply") && m.getParameterCount() == arity && !m.isBridge()) {
                found = m;
            }
        }
        if (found == null) {
            throw new ImplementationNotReached("the bound implementation declares no `apply` taking "
                    + arity + " argument(s)", new NoSuchMethodException("apply"));
        }
        found.setAccessible(true);
        return found;
    }

    private String baseOf(String behavior) {
        return baseOf(module, behavior);
    }

    /**
     * Whether {@code implementation} is an implementation of {@code module}'s {@code behavior}.
     *
     * <p>The same question this answerer asks of itself, for a reader that has to know which of a
     * module's rows a binding makes runnable before anything is run. Both go through
     * {@link #baseOf(String, String)}, so there is one place that decides how a behavior is spelled
     * as a class and it is the one the emitter uses.
     */
    static boolean isFor(Object implementation, String module, String behavior) {
        return everythingItIs(implementation.getClass()).contains(baseOf(module, behavior));
    }

    private static String baseOf(String module, String behavior) {
        return SoutherJvmAbi.nameOf(new GeneratedClass.BehaviorInterface(module, behavior))
                .binaryName();
    }

    /** Every class and interface the instance is, by binary name. Interfaces as well as classes: a
     *  single-input behavior's base is reached as a class, and what a later shape of the ABI makes a
     *  behavior's base is the ABI's to decide and not this walk's. */
    private static Set<String> everythingItIs(Class<?> type) {
        Set<String> names = new LinkedHashSet<>();
        Deque<Class<?>> todo = new ArrayDeque<>();
        todo.add(type);
        while (!todo.isEmpty()) {
            Class<?> next = todo.removeFirst();
            if (!names.add(next.getName())) {
                continue;
            }
            if (next.getSuperclass() != null) {
                todo.add(next.getSuperclass());
            }
            todo.addAll(List.of(next.getInterfaces()));
        }
        return names;
    }

    /** The class file of {@code binaryName} as the bound loader has it, or null where it has none.
     *  A loader is asked for the resource and not for the class: what is wanted is the bytes the
     *  declarations are stamped on, and loading would define a class nothing applies. */
    private static byte[] bytesOf(ClassLoader loader, String binaryName) {
        String resource = binaryName.replace('.', '/') + ".class";
        ClassLoader from = loader == null ? ClassLoader.getSystemClassLoader() : loader;
        try (InputStream in = from.getResourceAsStream(resource)) {
            return in == null ? null : in.readAllBytes();
        } catch (IOException _) {
            return null;
        }
    }
}
