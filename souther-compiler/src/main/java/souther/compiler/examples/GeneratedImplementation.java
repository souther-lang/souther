package souther.compiler.examples;

import souther.compiler.generated.GeneratedImplementations;
import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.observe.Applied;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.lang.reflect.Proxy;
import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

/**
 * The answerer a compile has of its own: the {@code $Impl} it emitted, constructed with the row's
 * stand-ins and applied, all in the loader the run built.
 *
 * <p>Everything here is a fact about that loader. Which class the behavior is, what its injecting
 * constructor takes, what a stand-in has to be to be taken by it, and how the behavior is entered —
 * none of it survives being asked about an implementation whose classes are some other loader's, which
 * is why it is here and not where a row is evaluated.
 *
 * <p>Which kind of behavior it is does not reach here. A {@code let} body and a {@code >->}
 * composition are both applied as the class their module emits, so a composition's stages run in order
 * and a case that leaves the main line is what the row sees, with no second implementation of what
 * {@code >->} means.
 */
final class GeneratedImplementation implements Answerer {

    private final GeneratedImplementations generated;
    private final MemoryClassLoader loader;

    GeneratedImplementation(GeneratedImplementations generated, MemoryClassLoader loader) {
        this.generated = generated;
        this.loader = loader;
    }

    /**
     * What this compile emitted for the behavior, if it emitted one.
     *
     * <p>Read off the manifest the emission produced. This compile applies what it generated, so what
     * it generated is the whole of the answer — and it is the emitter's own record of that rather than
     * the same decision made a second time from the module's declarations. The two agree today; the
     * one that is right the day they part is the emitter's.
     *
     * <p>A behavior it did generate is answered with {@link Answer.Something} whether or not the class
     * can be loaded. Loading is applying, and an implementation that was generated and cannot be
     * reached is {@link ImplementationNotReached} — a failure, and not this run having nothing to
     * apply.
     *
     * <p>What it crosses into is this compile's own declarations. The classes it applies are the ones
     * this compile emitted from the module the rows are written for, so there is no second build here
     * for a run to hold the first against.
     */
    @Override
    public Answer of(String behavior) {
        switch (generated.standingOf(behavior)) {
            case ELSEWHERE -> {
                return new Answer.Nothing();
            }
            case OWED_BUT_NOT_MADE -> {
                return new Answer.Unavailable();
            }
            case GENERATED -> { }
        }
        return new Answer.Something() {

            @Override
            public Origin origin() {
                return new TheCompilesOwn();
            }

            @Override
            public Applying applying(List<DependencyStandin> standins) {
                return GeneratedImplementation.this.applying(behavior, standins);
            }
        };
    }

    /**
     * The stand-ins made into what the injecting constructor takes, in the order it takes them.
     *
     * <p>Made here rather than when the behavior is applied, because a row whose stand-ins could not
     * be made never entered the behavior and its outcome has to say so.
     *
     * <p>What each stand-in has to be is read off the constructor the implementation was emitted
     * with, before any stand-in is made. The constructor's parameter is the fact; an instance is made
     * to be it, and is never what the parameter is worked out from.
     *
     * <p>An implementation that cannot be reached is still said where it is applied. No stand-in was
     * wrong, and a row said not to have been given one would name what did not happen.
     */
    private Applying applying(String behavior, List<DependencyStandin> standins) {
        Constructor<?> constructor;
        try {
            constructor = constructorOf(behavior);
        } catch (ReflectiveOperationException e) {
            return unreached(e);
        }
        Class<?>[] takes = constructor.getParameterTypes();
        if (takes.length != standins.size()) {
            throw new IllegalStateException("`" + behavior + "` is constructed with " + takes.length
                    + " dependencies and is handed " + standins.size() + " stand-ins");
        }
        Object[] instances = new Object[standins.size()];
        for (int i = 0; i < standins.size(); i++) {
            instances[i] = instanceOf(takes[i], standins.get(i));
        }
        return new Applying() {

            @Override
            public Applied applied() {
                return new Applied.GeneratedHere();
            }

            @Override
            public Object to(List<Handed> arguments) {
                return apply(constructor, instances, arguments);
            }
        };
    }

    /** The behavior whose implementation could not be reached, said so when it is applied. */
    private static Applying unreached(ReflectiveOperationException e) {
        return new Applying() {

            @Override
            public Applied applied() {
                return new Applied.GeneratedHere();
            }

            @Override
            public Object to(List<Handed> arguments) {
                throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
            }
        };
    }

    /**
     * The constructor the behavior's {@code $Impl} was emitted with, opened.
     *
     * <p>An implementation is emitted with one: the injecting constructor where it depends on
     * anything, and the one taking nothing where it does not.
     */
    private Constructor<?> constructorOf(String behavior) throws ReflectiveOperationException {
        Class<?> c = GeneratedClasses.load(loader,
                new GeneratedClass.BehaviorImpl(generated.module(), behavior));
        Constructor<?>[] declared = c.getDeclaredConstructors();
        if (declared.length != 1) {
            throw new NoSuchMethodException(c.getName() + " declares " + declared.length
                    + " constructors, and an implementation is emitted with one");
        }
        declared[0].setAccessible(true);
        return declared[0];
    }

    /**
     * A stand-in as what the constructor takes for it, {@code held}.
     *
     * <p>An interface is proxied, and an abstract base is extended by a generated subclass. Which a
     * dependency is held as is the ABI's answer ({@code codegen.BehaviorAbi}) — the unary
     * {@code Behavior}, a Java-supplied behavior's base, or a Souther-implemented behavior's own
     * interface — and this reads the answer rather than giving it a second time from how many inputs
     * the dependency takes or who implements it. A {@code with} and a table both arrive here, so
     * neither assumes either.
     */
    private Object instanceOf(Class<?> held, DependencyStandin standin) {
        Method answering = answeredBy(held, standin);
        return held.isInterface()
                ? proxyOf(held, answering, standin.answers())
                : subclassOf(held, answering, standin);
    }

    /**
     * The method a stand-in held as {@code held} answers: the one abstract method a behavior's class
     * has, whichever of the ABI's forms it is. A class with none or with several is not one the ABI
     * makes, and a stand-in that picked one of several would be answering for a method nothing said
     * it stands for.
     */
    private static Method answeredBy(Class<?> held, DependencyStandin standin) {
        List<Method> abstracts = Arrays.stream(held.getMethods())
                .filter(m -> Modifier.isAbstract(m.getModifiers()))
                .toList();
        if (abstracts.size() != 1) {
            throw new StandinNotBuilt(standin.dependency(), "`" + held.getName() + "` has "
                    + abstracts.size() + " abstract methods, and a behavior's class has the one it"
                    + " is applied by");
        }
        return abstracts.getFirst();
    }

    /**
     * Applies the behavior. The row it belongs to is what carries the budget: recursion is total by
     * default, so most code cannot loop, and a `partial` recursion that does not terminate is bounded
     * there along with everything else the row runs.
     *
     * <p>The public name is an interface; the fields, constructor and erased apply live on its
     * {@code $Impl} (spec §jvm-anonymous-union). A behavior its module does not expose generates a
     * package-private class, and an {@code example} runs inside the module rather than across its
     * boundary, so exposure does not decide whether it can be evaluated — the declared members are
     * taken and opened.
     */
    private Object apply(Constructor<?> constructor, Object[] fakes, List<Handed> arguments) {
        Object[] args = new Object[arguments.size()];
        for (int i = 0; i < args.length; i++) {
            // The value as this compile built it: these are the classes being applied, so nothing
            // crosses and nothing is read back into a neutral form on the way in.
            args[i] = arguments.get(i).built();
        }
        Object instance;
        Method apply;
        try {
            instance = constructor.newInstance(fakes);
            Class<?>[] paramTypes = new Class<?>[args.length];
            Arrays.fill(paramTypes, Object.class);
            apply = constructor.getDeclaringClass().getDeclaredMethod("apply", paramTypes);
            apply.setAccessible(true);
        } catch (InvocationTargetException ite) {
            // The constructor ran and threw. That is the model's code, so it goes out the way the
            // behavior's own failure does — unless it is a class of this compile failing to link,
            // which is not the model's.
            throw InvocationFailure.ofGeneratedCode(ite.getCause());
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
        }
        try {
            return apply.invoke(instance, args);
        } catch (InvocationTargetException ite) {
            // What the applied code came back with, carried out as it stands. Whose failure it is and
            // what it means for the row are read where the row is. The classes are this compile's
            // own, so one that will not link is its output failing and is said so before it is
            // carried as something the applied code ended with.
            throw InvocationFailure.ofGeneratedCode(ite.getCause());
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
        }
    }

    /**
     * A proxy of the interface {@code held} whose {@code answering} runs {@code answers}, and which
     * is the object it is for {@code Object}'s methods.
     *
     * <p>Defined by the loader that defined the interface. A behavior its module does not expose has
     * a package-private interface, and a proxy of one has to be in its package and its loader.
     *
     * <p>Anything else it is asked is refused rather than answered with nothing. {@link #answeredBy}
     * found the one method the class has, so another is a class this compile did not make.
     */
    private static Object proxyOf(Class<?> held, Method answering,
                                  Function<Object[], Object> answers) {
        return Proxy.newProxyInstance(held.getClassLoader(), new Class<?>[] {held}, (proxy, method, a) -> {
            if (method.equals(answering)) {
                return answers.apply(a == null ? new Object[0] : a);
            }
            if (method.getDeclaringClass() == Object.class) {
                return switch (method.getName()) {
                    case "toString" -> "a stand-in for " + held.getName();
                    case "hashCode" -> System.identityHashCode(proxy);
                    default -> proxy == a[0];
                };
            }
            throw new IllegalStateException("a stand-in for " + held.getName() + " answers "
                    + answering + ", and was asked " + method);
        });
    }

    /**
     * Generates (once) and instantiates a subclass of the abstract base {@code base}, whose typed
     * {@code apply} packs its arguments into an {@code Object[]} and delegates to what the stand-in
     * answers.
     *
     * <p>The subclass is named for the dependency, in the module that declares it, which is where its
     * base was generated (spec §java-base-class) and not always the module being applied.
     */
    private Object subclassOf(Class<?> base, Method answering, DependencyStandin standin) {
        GeneratedClass.BehaviorInterface baseClass = new GeneratedClass.BehaviorInterface(
                standin.dependency().module(), standin.dependency().name());
        try {
            String fakeName = SoutherJvmAbi.nameOf(new GeneratedClass.ExampleFake(baseClass)).binaryName();
            Class<?> fakeClass = loader.define(fakeName,
                    () -> fakeSubclassBytes(fakeName, base, answering));
            return fakeClass.getConstructor(Function.class).newInstance(standin.answers());
        } catch (ReflectiveOperationException e) {
            throw new StandinNotBuilt(standin.dependency(),
                    "its base subclass could not be built: " + e);
        }
    }

    private byte[] fakeSubclassBytes(String fakeName, Class<?> base, Method apply) {
        java.lang.constant.ClassDesc cdFake = java.lang.constant.ClassDesc.of(fakeName);
        java.lang.constant.ClassDesc cdBase = java.lang.constant.ClassDesc.of(base.getName());
        java.lang.constant.ClassDesc cdFunc =
                java.lang.constant.ClassDesc.of("java.util.function.Function");
        java.lang.constant.ClassDesc cdObject = java.lang.constant.ConstantDescs.CD_Object;
        java.lang.constant.ClassDesc[] paramDescs = new java.lang.constant.ClassDesc[apply.getParameterCount()];
        for (int i = 0; i < paramDescs.length; i++) {
            paramDescs[i] = apply.getParameterTypes()[i].describeConstable().orElseThrow();
        }
        java.lang.constant.ClassDesc retDesc = apply.getReturnType().describeConstable().orElseThrow();
        java.lang.constant.MethodTypeDesc applyDesc = java.lang.constant.MethodTypeDesc.of(retDesc, paramDescs);
        java.lang.constant.MethodTypeDesc voidCtor =
                java.lang.constant.MethodTypeDesc.of(java.lang.constant.ConstantDescs.CD_void);
        java.lang.constant.MethodTypeDesc funcApply =
                java.lang.constant.MethodTypeDesc.of(cdObject, cdObject);
        return java.lang.classfile.ClassFile.of().build(cdFake, cb -> {
            cb.withSuperclass(cdBase);
            cb.withFlags(java.lang.classfile.ClassFile.ACC_PUBLIC | java.lang.classfile.ClassFile.ACC_FINAL
                    | java.lang.classfile.ClassFile.ACC_SUPER);
            cb.withField("body", cdFunc, java.lang.classfile.ClassFile.ACC_PRIVATE
                    | java.lang.classfile.ClassFile.ACC_FINAL);
            cb.withMethodBody("<init>",
                    java.lang.constant.MethodTypeDesc.of(java.lang.constant.ConstantDescs.CD_void, cdFunc),
                    java.lang.classfile.ClassFile.ACC_PUBLIC, code -> {
                        code.aload(0);
                        code.invokespecial(cdBase, "<init>", voidCtor);
                        code.aload(0);
                        code.aload(1);
                        code.putfield(cdFake, "body", cdFunc);
                        code.return_();
                    });
            cb.withMethodBody("apply", applyDesc, java.lang.classfile.ClassFile.ACC_PUBLIC, code -> {
                code.aload(0);
                code.getfield(cdFake, "body", cdFunc);
                code.loadConstant(paramDescs.length);
                code.anewarray(cdObject);
                for (int i = 0; i < paramDescs.length; i++) {
                    code.dup();
                    code.loadConstant(i);
                    code.aload(i + 1);   // every apply param is a reference (Int boxes to Long, etc.)
                    code.aastore();
                }
                code.invokeinterface(cdFunc, "apply", funcApply);
                if (!retDesc.equals(cdObject)) {
                    code.checkcast(retDesc);
                }
                code.areturn();
            });
        });
    }
}
