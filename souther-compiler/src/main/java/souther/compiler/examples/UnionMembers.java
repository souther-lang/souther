package souther.compiler.examples;

import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.SumCases;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
import souther.compiler.jvm.JvmClassNames;
import souther.compiler.jvm.SoutherJvmAbi;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.invoke.MethodType;
import java.lang.reflect.Constructor;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The two conversions between a Souther value and a behavior's answer as the JVM carries it, for a
 * run of rows: the two {@code codegen.ResultBoundary} emits, done on loaded classes.
 *
 * <p>A member the behavior's module declared is a member of its union as it is; a primitive and a
 * type another module declares reach the union through a bridge case that module emits (spec
 * §jvm-anonymous-union). Which members those are is {@link JvmClassNames#bridgedMembers}, the answer
 * the emitted classes were made by, and what a bridge case is called is the ABI's. Nothing here
 * decides either.
 *
 * <p>A stand-in's answer goes in ({@link #asAMember}): it is built as the Souther value, and a
 * caller holding the dependency by its typed {@code apply} is declared to receive the member. A
 * behavior's answer comes out ({@link #asTheValue}): a row writes the value, not the bridge case.
 *
 * <p>Out by the name of the class, in by the class. An answer may be of another loader's classes —
 * what an implementation supplied from outside answers with — and is read by the name its class
 * carries, as every reading of an answer is ({@link Answerer.Applying#to}). A stand-in is of this
 * compile's classes, and what it is made into is a class of this loader.
 *
 * <p>One for a run, beside {@link EnsuresChecks} and for the same reason: which members a union
 * carries in which class is a fact about the behavior and this loader, so it is worked out once per
 * behavior and not once per row. Concurrent because a row is a thread.
 */
final class UnionMembers {

    private final ClassLoader loader;
    private final DeclarationKinds kinds;
    private final SumCases sums;
    private final Map<ValueName.Behavior, List<String>> bridgeNames = new ConcurrentHashMap<>();
    private final Map<ValueName.Behavior, Making> makings = new ConcurrentHashMap<>();

    UnionMembers(ClassLoader loader, DeclarationKinds kinds, SumCases sums) {
        this.loader = loader;
        this.kinds = kinds;
        this.sums = sums;
    }

    /**
     * {@code value}, which {@code behavior} answering {@code out} answers with, as the member of
     * its union it is — the value itself for a member the behavior's module declared, the bridge
     * case holding it otherwise.
     *
     * @throws IllegalStateException where {@code value} is no member of the union, or a class the
     *                               union is answered through is not in this compile's classes:
     *                               both are this compiler failing, and neither is anything a
     *                               stand-in says
     */
    Object asAMember(ValueName.Behavior behavior, Type out, Object value) {
        if (!(out instanceof Type.Union)) {
            return value;
        }
        return makings.computeIfAbsent(behavior, _ -> making(behavior, out)).of(value);
    }

    /**
     * The Souther value {@code answered} is, {@code behavior} answering {@code out}: what a bridge
     * case holds, and anything else as it is.
     */
    Object asTheValue(ValueName.Behavior behavior, Type out, Object answered) {
        if (answered == null) {
            return null;
        }
        String carried = answered.getClass().getName();
        for (String bridge : bridgeNames.computeIfAbsent(behavior, _ -> named(behavior, out))) {
            if (bridge.equals(carried)) {
                try {
                    return answered.getClass().getMethod("value").invoke(answered);
                } catch (ReflectiveOperationException e) {
                    throw new IllegalStateException("a bridge case with no `value`: " + carried, e);
                }
            }
        }
        return answered;
    }

    /** The binary names of the bridge cases {@code behavior}'s union is answered through. */
    private List<String> named(ValueName.Behavior behavior, Type out) {
        List<String> names = new ArrayList<>();
        for (TypeSymbol member : bridged(behavior, out)) {
            names.add(SoutherJvmAbi.nameOf(bridgeOf(behavior, member)).binaryName());
        }
        return names;
    }

    private List<TypeSymbol> bridged(ValueName.Behavior behavior, Type out) {
        return JvmClassNames.bridgedMembers(behavior.module(), out, kinds, sums);
    }

    private static GeneratedClass.BridgeCase bridgeOf(ValueName.Behavior behavior,
                                                      TypeSymbol member) {
        return new GeneratedClass.BridgeCase(behavior.module(), member);
    }

    /** How a value is made a member of {@code behavior}'s union, held to belong to it. */
    private Making making(ValueName.Behavior behavior, Type out) {
        Class<?> union = loaded(new GeneratedClass.BehaviorResult(behavior.module(), behavior.name()));
        List<Bridge> bridges = new ArrayList<>();
        for (TypeSymbol member : bridged(behavior, out)) {
            Class<?> bridge = loaded(bridgeOf(behavior, member));
            Constructor<?>[] made = bridge.getConstructors();
            if (!union.isAssignableFrom(bridge) || made.length != 1
                    || made[0].getParameterCount() != 1) {
                throw new IllegalStateException("`" + bridge.getName() + "` is not a bridge case of `"
                        + union.getName() + "` holding the one value of `" + member + "`");
            }
            bridges.add(new Bridge(
                    MethodType.methodType(made[0].getParameterTypes()[0]).wrap().returnType(),
                    made[0]));
        }
        return new Making(union, List.copyOf(bridges));
    }

    /** A class this compile emitted, loaded. */
    private Class<?> loaded(GeneratedClass generated) {
        try {
            return GeneratedClasses.load(loader, generated);
        } catch (ClassNotFoundException e) {
            throw new IllegalStateException("`" + SoutherJvmAbi.nameOf(generated).binaryName()
                    + "` is not in this compile's classes", e);
        }
    }

    /** A bridge case: the class of the value it holds, and what makes one of it. */
    private record Bridge(Class<?> holds, Constructor<?> made) {}

    /** A union, and the bridge cases it is answered through. */
    private record Making(Class<?> union, List<Bridge> bridges) {

        /** {@code value} as a member of {@link #union}, which it is on every way out. */
        Object of(Object value) {
            if (union.isInstance(value)) {
                return value;
            }
            for (Bridge bridge : bridges) {
                if (bridge.holds().isInstance(value)) {
                    try {
                        return bridge.made().newInstance(value);
                    } catch (ReflectiveOperationException e) {
                        throw new IllegalStateException("the bridge case "
                                + bridge.made().getName() + " did not take the value it holds", e);
                    }
                }
            }
            throw new IllegalStateException(value + " is no member of " + union.getName()
                    + ", nor held by any of its bridge cases");
        }
    }
}
