package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.runtime.WorkCheckpoint;
import souther.test.ClosedWorldContract;

import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.constantpool.PoolEntry;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.invoke.MethodHandles;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A class generated for an evaluation hands the evaluation's checkpoint to every runtime operation
 * that takes one, and a class that ships names neither the checkpoint nor the compiler.
 *
 * <p>Asked of the class files the conformance corpus compiles to, and one model of the boundary
 * shapes it does not write, both generations of every module, and of the runtime itself rather than
 * of a list written here. Where the runtime has an entry of
 * the same name taking what a call takes and a checkpoint last, the operation is one whose work
 * grows with what it is handed, and an evaluated class calling or binding the entry without it is a
 * call the evaluation cannot stop — whichever emitter wrote it, including one added later. The JDK
 * methods named here are the ones whose work grows with the text or the values they are handed and
 * that an evaluated class reaches through the runtime instead.
 */
@ClosedWorldContract
class AnEvaluatedClassHandsItsCheckpointToEveryRuntimeCallThatTakesOneTest {

    private static final String CHECKPOINT = WorkCheckpoint.class.getName().replace('.', '/');

    /** JDK methods an evaluated class reaches through the runtime, by owner and name. */
    private static final Map<String, Set<String>> WALKS_IN_THE_HOST = Map.of(
            "java/lang/String", Set.of("contains", "startsWith", "endsWith", "indexOf", "compareTo"),
            "java/lang/Comparable", Set.of("compareTo"),
            "java/util/function/Predicate", Set.of("test"));

    @Test
    void anEvaluatedClassTakesTheEntryThatPassesTheCheckpoint() {
        List<String> missed = new ArrayList<>();
        int runtimeCalls = 0;
        int handedACheckpoint = 0;
        for (Map.Entry<String, ClassFileImage> each : evaluatedClasses().entrySet()) {
            for (MethodModel method : parse(each.getValue()).methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                for (CodeElement element : method.code().get()) {
                    for (Reached reached : reached(element)) {
                        if (!reached.owner().startsWith("souther/runtime/")) {
                            if (WALKS_IN_THE_HOST.getOrDefault(reached.owner(), Set.of()).contains(reached.name())) {
                                missed.add(where(each.getKey(), method) + " calls the host's " + reached);
                            }
                            continue;
                        }
                        runtimeCalls++;
                        if (reached.type().parameterCount() > 0 && reached.type().parameterType(
                                reached.type().parameterCount() - 1).descriptorString().equals("L" + CHECKPOINT + ";")) {
                            handedACheckpoint++;
                            if (!exists(reached)) {
                                missed.add(where(each.getKey(), method) + " hands a checkpoint to " + reached
                                        + ", which the runtime does not have");
                            }
                        } else if (takesACheckpoint(reached)) {
                            missed.add(where(each.getKey(), method) + " reaches " + reached
                                    + " without the checkpoint its other entry takes");
                        }
                    }
                }
            }
        }
        assertEquals(List.of(), missed);
        assertTrue(runtimeCalls > 0 && handedACheckpoint > 0,
                "the evaluated classes reach the runtime (" + runtimeCalls + ") and hand a checkpoint ("
                        + handedACheckpoint + "), so an empty list above means something");
    }

    @Test
    void aClassThatShipsNamesNeitherTheCheckpointNorTheCompiler() {
        List<String> naming = new ArrayList<>();
        int read = 0;
        for (Map.Entry<String, ClassFileImage> each : shippedClasses().entrySet()) {
            read++;
            for (PoolEntry entry : parse(each.getValue()).constantPool()) {
                if (entry instanceof ClassEntry named) {
                    String name = named.asInternalName();
                    if (name.equals(CHECKPOINT) || name.startsWith("souther/compiler/")) {
                        naming.add(each.getKey() + " names " + name);
                    }
                }
            }
        }
        assertEquals(List.of(), naming);
        assertTrue(read > 0, "classes that ship were read");
    }

    /** A method a call or a binding reaches. */
    private record Reached(String owner, String name, MethodTypeDesc type) {
        @Override
        public String toString() {
            return owner + "." + name + type.descriptorString();
        }
    }

    /** What {@code element} reaches: the method an invocation calls, or the methods an
     *  {@code invokedynamic} binds among its bootstrap's arguments. */
    private static List<Reached> reached(CodeElement element) {
        List<Reached> out = new ArrayList<>();
        if (element instanceof InvokeInstruction invoke) {
            out.add(new Reached(invoke.owner().asInternalName(), invoke.name().stringValue(),
                    invoke.typeSymbol()));
        } else if (element instanceof InvokeDynamicInstruction indy) {
            for (ConstantDesc argument : indy.bootstrapArgs()) {
                if (argument instanceof DirectMethodHandleDesc handle) {
                    out.add(new Reached(handle.owner().descriptorString()
                            .substring(1, handle.owner().descriptorString().length() - 1),
                            handle.methodName(), handle.invocationType().dropParameterTypes(0, 0)));
                }
            }
        }
        return out;
    }

    /** Whether the runtime class {@code reached} names has a public static of the same name taking
     *  what it takes and a checkpoint after. */
    private static boolean takesACheckpoint(Reached reached) {
        Class<?>[] takes = parameters(reached);
        Class<?>[] counted = Arrays.copyOf(takes, takes.length + 1);
        counted[takes.length] = WorkCheckpoint.class;
        return hasStatic(reached, counted);
    }

    /** Whether the runtime class {@code reached} names has the public static it reaches. */
    private static boolean exists(Reached reached) {
        return hasStatic(reached, parameters(reached));
    }

    private static boolean hasStatic(Reached reached, Class<?>[] takes) {
        for (Method candidate : owner(reached).getMethods()) {
            if (Modifier.isStatic(candidate.getModifiers()) && candidate.getName().equals(reached.name())
                    && Arrays.equals(candidate.getParameterTypes(), takes)) {
                return true;
            }
        }
        return false;
    }

    private static Class<?> owner(Reached reached) {
        try {
            return Class.forName(reached.owner().replace('/', '.'));
        } catch (ClassNotFoundException e) {
            throw new IllegalStateException("the runtime has no class a class reaches: " + reached, e);
        }
    }

    private static Class<?>[] parameters(Reached reached) {
        try {
            return reached.type().resolveConstantDesc(MethodHandles.publicLookup()).parameterArray();
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("what a class reaches names types nobody has: " + reached, e);
        }
    }

    private static String where(String className, MethodModel method) {
        return className + "." + method.methodName().stringValue();
    }

    private static ClassModel parse(ClassFileImage image) {
        return ClassFile.of().parse(image.bytes());
    }

    private static Map<String, ClassFileImage> evaluatedClasses() {
        Map<String, ClassFileImage> out = new LinkedHashMap<>();
        for (Compilation compilation : corpora()) {
            for (String module : compilation.modules()) {
                var artifact = compilation.db().ask(new Output.Evaluated(module, ArmObservation.OMIT)).value();
                if (artifact != null) {
                    out.putAll(artifact.classes());
                }
            }
        }
        return out;
    }

    private static Map<String, ClassFileImage> shippedClasses() {
        Map<String, ClassFileImage> out = new LinkedHashMap<>();
        for (Compilation compilation : corpora()) {
            for (String module : compilation.modules()) {
                Map<String, ClassFileImage> classes = compilation.db().ask(new Output.Classes(module)).value();
                if (classes != null) {
                    out.putAll(classes);
                }
            }
        }
        return out;
    }

    /**
     * The boundary shapes the conformance corpus does not write: a collection inside a collection,
     * a set and a map whose key is a newtype at the boundary, and an amount. Their decoders and
     * encoders bind runtime operations as functions, which is the other way a class reaches the
     * runtime, and without them that way would be asked of no class here.
     */
    private static final String NESTED = """
            module example.nested
            data Code = String
            data Label = String
            data In = {
                byOwner: Map<String, List<Code>>
                , tags: Map<String, Set<Label>>
                , stocks: List<Map<Code, Int>>
                , kinds: Set<String>
                , amount: Decimal
            }
            data Out = {
                byOwner: Map<String, List<Code>>
                , tags: Map<String, Set<Label>>
                , stocks: List<Map<Code, Int>>
                , kinds: Set<String>
                , amount: Decimal
            }
            behavior run : (i: In) -> Out constructs Out
            let run (i) = Out {
                byOwner = i.byOwner,
                tags = i.tags,
                stocks = i.stocks,
                kinds = i.kinds,
                amount = i.amount
            }
            """;

    private static List<Compilation> corpora;

    private static List<Compilation> corpora() {
        if (corpora != null) {
            return corpora;
        }
        List<Compilation> out = new ArrayList<>();
        Compilation nested = Compilation.ofSource(NESTED, "Main");
        nested.answerEverything();
        out.add(nested);
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            Map<String, String> byId = new LinkedHashMap<>();
            for (int i = 0; i < corpus.sources().size(); i++) {
                byId.put(corpus.files().get(i), corpus.sources().get(i));
            }
            Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
            c.answerEverything();
            out.add(c);
        }
        corpora = List.copyOf(out);
        return corpora;
    }
}
