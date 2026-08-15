package souther.compiler.examples;

import souther.compiler.generated.MemoryClassLoader;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.observe.Applied;

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

    private final String module;
    private final MemoryClassLoader loader;

    GeneratedImplementation(String module, MemoryClassLoader loader) {
        this.module = module;
        this.loader = loader;
    }

    @Override
    public Applied applied() {
        return new Applied.GeneratedHere();
    }

    /**
     * The stand-ins made into what the injecting constructor takes, in the order it takes them.
     *
     * <p>Made here rather than when the behavior is applied, because a row whose stand-ins could not
     * be made never entered the behavior and its outcome has to say so.
     */
    @Override
    public Applying applying(String behavior, List<DependencyStandin> standins) {
        Object[] instances = new Object[standins.size()];
        for (int i = 0; i < standins.size(); i++) {
            instances[i] = instanceOf(standins.get(i));
        }
        return arguments -> apply(behavior, instances, arguments);
    }

    /**
     * A stand-in as the injected instance: a unary {@code Behavior} proxy for a single-input
     * dependency, or a runtime-generated subclass of the standalone base for one taking any other
     * count (whose typed {@code apply} the unary {@code Behavior} cannot stand in for; issue #57).
     * Both the table and the constant {@code with} stand-in route through here, so neither path assumes
     * an arity.
     */
    private Object instanceOf(DependencyStandin standin) {
        return standin.inputs() == 1
                ? behaviorProxy(standin.answers())
                : standaloneInstance(standin);
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
    private Object apply(String behavior, Object[] fakes, List<Handed> arguments) {
        Object[] args = new Object[arguments.size()];
        for (int i = 0; i < args.length; i++) {
            // The value as this compile built it: these are the classes being applied, so nothing
            // crosses and nothing is read back into a neutral form on the way in.
            args[i] = arguments.get(i).built();
        }
        Class<?> c;
        Object instance;
        java.lang.reflect.Method apply;
        try {
            c = GeneratedClasses.load(loader, new GeneratedClass.BehaviorImpl(module, behavior));
            if (fakes.length == 0) {
                instance = openCtor(c).newInstance();
            } else {
                // the injecting constructor takes one param per dependency: the unary Behavior for a
                // single-input dep (a Proxy), or the dep's own base class for a multi-input dep (a
                // generated subclass) — issue #57. The fake's runtime type tells the two apart.
                Class<?> behaviorIface = loader.loadClass("souther.runtime.Behavior");
                Class<?>[] ctorParams = new Class<?>[fakes.length];
                for (int i = 0; i < fakes.length; i++) {
                    ctorParams[i] = behaviorIface.isInstance(fakes[i])
                            ? behaviorIface
                            : fakes[i].getClass().getSuperclass();
                }
                instance = openCtor(c, ctorParams).newInstance(fakes);
            }
            Class<?>[] paramTypes = new Class<?>[args.length];
            java.util.Arrays.fill(paramTypes, Object.class);
            apply = c.getDeclaredMethod("apply", paramTypes);
            apply.setAccessible(true);
        } catch (java.lang.reflect.InvocationTargetException ite) {
            // The constructor ran and threw. That is the model's code, so it goes out the way the
            // behavior's own failure does.
            throw new InvocationFailure(ite.getCause());
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
        }
        try {
            return apply.invoke(instance, args);
        } catch (java.lang.reflect.InvocationTargetException ite) {
            // What the applied code came back with, carried out as it stands. Whose failure it is and
            // what it means for the row are read where the row is.
            throw new InvocationFailure(ite.getCause());
        } catch (ReflectiveOperationException e) {
            throw new ImplementationNotReached(String.valueOf(e.getMessage()), e);
        }
    }

    /** The {@code $Impl}'s constructor, opened. */
    private static java.lang.reflect.Constructor<?> openCtor(Class<?> c, Class<?>... params)
            throws ReflectiveOperationException {
        java.lang.reflect.Constructor<?> ctor = c.getDeclaredConstructor(params);
        ctor.setAccessible(true);
        return ctor;
    }

    /** A {@code Behavior} proxy whose {@code apply} runs {@code answers}. Reflective so the runtime
     * (souther-runtime, `provided`) may be absent, in which case the LinkageError is caught upstream. */
    private Object behaviorProxy(Function<Object[], Object> answers) {
        Class<?> iface;
        try {
            iface = loader.loadClass("souther.runtime.Behavior");
        } catch (ClassNotFoundException _) {
            throw new NoClassDefFoundError("souther.runtime.Behavior");
        }
        return java.lang.reflect.Proxy.newProxyInstance(loader, new Class<?>[] {iface}, (proxy, method, a) -> {
            if (method.getName().equals("apply")) {
                return answers.apply(a == null ? new Object[0] : a);
            }
            return switch (method.getName()) {
                case "toString" -> "fake";
                case "hashCode" -> System.identityHashCode(proxy);
                case "equals" -> proxy == (a != null && a.length > 0 ? a[0] : null);
                default -> null;
            };
        });
    }

    /** Generates (once) and instantiates a subclass of a standalone injected base whose typed
     * {@code apply} packs its arguments into an {@code Object[]} and delegates to what the stand-in
     * answers. */
    private Object standaloneInstance(DependencyStandin standin) {
        GeneratedClass.BehaviorInterface baseClass =
                new GeneratedClass.BehaviorInterface(module, standin.dependency());
        try {
            Class<?> base = GeneratedClasses.load(loader, baseClass);
            java.lang.reflect.Method apply = null;
            for (java.lang.reflect.Method m : base.getDeclaredMethods()) {
                if (m.getName().equals("apply") && java.lang.reflect.Modifier.isAbstract(m.getModifiers())) {
                    apply = m;
                }
            }
            if (apply == null) {
                throw new NoSuchMethodException("abstract apply on " + base.getName());
            }
            String fakeName = SoutherJvmAbi.nameOf(new GeneratedClass.ExampleFake(baseClass)).binaryName();
            java.lang.reflect.Method applyM = apply;
            Class<?> fakeClass = loader.define(fakeName, () -> fakeSubclassBytes(fakeName, base, applyM));
            return fakeClass.getConstructor(Function.class).newInstance(standin.answers());
        } catch (ReflectiveOperationException e) {
            throw new StandinNotBuilt(standin.dependency(),
                    "its base subclass could not be built: " + e);
        }
    }

    private byte[] fakeSubclassBytes(String fakeName, Class<?> base, java.lang.reflect.Method apply) {
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
