package souther.compiler.examples;

import souther.compiler.check.AtomSpace;
import souther.compiler.check.DeclarationKinds;
import souther.compiler.check.SumCases;
import souther.compiler.jvm.GeneratedClass;
import souther.compiler.jvm.GeneratedClasses;
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
import java.util.function.UnaryOperator;

/**
 * The member of its union a stand-in's answer is handed back as.
 *
 * <p>A behavior answers a union as the JVM carries it. A case the behavior's module declares is a
 * member as it is; a primitive and a type another module declares reach the union through a bridge
 * case that module emits (spec §jvm-anonymous-union). A fixture is built as the Souther value, so a
 * stand-in answering one of those hands back the bridge case holding it — which is what a caller
 * holding the dependency by its typed {@code apply} is declared to receive, and what it reads the
 * value back out of.
 *
 * <p>The members are walked by the rule a caller's projection of the behavior is made by, and
 * {@link ExampleVerifier#projected} undoes this.
 *
 * <p>One for a run, beside {@link EnsuresChecks} and for the same reason: which class carries which
 * member is a fact about the behavior and this loader, so it is worked out once per behavior rather
 * than once per stand-in, which is once per row. Concurrent because a row is a thread.
 */
final class UnionMembers {

    private final ClassLoader loader;
    private final DeclarationKinds kinds;
    private final SumCases sums;
    private final Map<ValueName.Behavior, UnaryOperator<Object>> found = new ConcurrentHashMap<>();

    UnionMembers(ClassLoader loader, DeclarationKinds kinds, SumCases sums) {
        this.loader = loader;
        this.kinds = kinds;
        this.sums = sums;
    }

    /**
     * What makes a value a stand-in for {@code behavior} answers into the member of its union
     * {@code out} that the behavior answers with.
     *
     * @param out the behavior's own output, which is the same for every stand-in for it
     * @throws IllegalStateException where a class the union is answered through is not in this
     *                               compile's classes, which is its emission failing and nothing a
     *                               stand-in says
     */
    UnaryOperator<Object> of(ValueName.Behavior behavior, Type out) {
        return found.computeIfAbsent(behavior, _ -> made(behavior, out));
    }

    private UnaryOperator<Object> made(ValueName.Behavior behavior, Type out) {
        if (!(out instanceof Type.Union)) {
            return UnaryOperator.identity();
        }
        Class<?> union = loaded(new GeneratedClass.BehaviorResult(behavior.module(), behavior.name()));
        List<Constructor<?>> bridges = new ArrayList<>();
        for (TypeSymbol member : AtomSpace.subjectAtoms(out, kinds, sums)) {
            if (!member.isDeclaredByLanguage() && member instanceof TypeSymbol.AtModule at
                    && at.module().equals(behavior.module())) {
                continue;
            }
            Constructor<?>[] made = loaded(new GeneratedClass.BridgeCase(behavior.module(), member))
                    .getConstructors();
            if (made.length != 1 || made[0].getParameterCount() != 1) {
                throw new IllegalStateException("the bridge case of `" + member + "` in `"
                        + behavior + "`'s union is not built from the one value it holds");
            }
            bridges.add(made[0]);
        }
        List<Class<?>> holds = bridges.stream()
                .<Class<?>>map(bridge -> MethodType.methodType(bridge.getParameterTypes()[0])
                        .wrap().returnType())
                .toList();
        return value -> {
            if (union.isInstance(value)) {
                return value;
            }
            for (int i = 0; i < bridges.size(); i++) {
                if (holds.get(i).isInstance(value)) {
                    try {
                        return bridges.get(i).newInstance(value);
                    } catch (ReflectiveOperationException e) {
                        throw new IllegalStateException("the bridge case "
                                + bridges.get(i).getName() + " did not take the value it holds", e);
                    }
                }
            }
            return value;
        };
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
}
