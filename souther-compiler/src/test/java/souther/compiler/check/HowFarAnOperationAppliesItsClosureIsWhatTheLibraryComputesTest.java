package souther.compiler.check;

import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.decode.Decoder;
import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.DefaultStdlib;
import souther.compiler.Emitted;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.semantics.Combinator;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.runtime.Behavior;
import souther.runtime.ConstraintViolation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How far each operation goes applying the closure it is handed is what the library computes.
 *
 * <p>Where an operation stops is declared beside what its signature says it hands the closure
 * ({@link Combinator#applied}), and a statement inside the closure is read as reached on an element
 * only where the operation would get that far. So the declaration is held to a run: each operation
 * whose closure answers a truth is run over a container whose first element the closure answers
 * once true and once false, and whose second element aborts the closure. Whether the run aborted
 * is whether the operation went on to the second element.
 *
 * <p>Every operation that hands a closure what a container holds is asked, and one whose closure
 * answers anything but a truth has nothing to stop on: it is held to being declared as applying its
 * closure to every element.
 */
class HowFarAnOperationAppliesItsClosureIsWhatTheLibraryComputesTest {

    /** What a run of each kind of operation does: aborts where the closure holds of the first
     *  element, and where it fails of it. */
    private record Ran(boolean abortedPastAHolding, boolean abortedPastAFailing) {}

    private static final Map<HowAClosureIsApplied, Ran> DECLARED = Map.of(
            HowAClosureIsApplied.TO_EVERY_ELEMENT, new Ran(true, true),
            HowAClosureIsApplied.UNTIL_ONE_HOLDS, new Ran(false, true),
            HowAClosureIsApplied.UNTIL_ONE_FAILS, new Ran(true, false));

    @Test
    void everyOperationStopsWhereItIsDeclaredToAndNowhereElse() throws Exception {
        Map<String, HowAClosureIsApplied> declared = new TreeMap<>();
        Map<String, HowAClosureIsApplied> ran = new TreeMap<>();
        List<String> unwritten = new ArrayList<>();
        int truths = 0;
        for (ValueName.Stdlib.Operation operation : Combinators.named()) {
            Combinator rule = Combinators.of(operation);
            Stdlib.Entry entry = DefaultStdlib.get().entry(operation);
            // A sugar has no declaration and is answered with what it rewrites to, which is
            // asked under its own name.
            if (entry == null) {
                continue;
            }
            Stdlib.Signature signature = entry.signature();
            String name = operation.alias() + "." + operation.name();
            if (!(signature.params().get(rule.closureArg()) instanceof Type.FnOf closure)
                    || !Type.BOOL.equals(closure.result())) {
                declared.put(name, rule.applied());
                ran.put(name, HowAClosureIsApplied.TO_EVERY_ELEMENT);
                continue;
            }
            String holding = call(name, signature, rule, closure, "==");
            String failing = call(name, signature, rule, closure, "/=");
            if (holding == null || failing == null) {
                unwritten.add(name);
                continue;
            }
            truths++;
            Ran run = new Ran(aborts(holding), aborts(failing));
            declared.put(name, rule.applied());
            ran.put(name, DECLARED.entrySet().stream()
                    .filter(each -> each.getValue().equals(run))
                    .map(Map.Entry::getKey).findFirst().orElse(null));
        }
        assertEquals(List.of(), unwritten, "an operation whose arguments this cannot write");
        assertEquals(declared, ran);
        // The run is what is asked, so it has to have asked something of operations that stop and
        // of ones that do not.
        assertEquals(true, truths > 0 && ran.containsValue(HowAClosureIsApplied.UNTIL_ONE_HOLDS)
                && ran.containsValue(HowAClosureIsApplied.UNTIL_ONE_FAILS)
                && ran.containsValue(HowAClosureIsApplied.TO_EVERY_ELEMENT));
    }

    /**
     * A module running {@code name} once, its closure answering {@code 1 mod element} against
     * nought by {@code relation}: of the first element, one, that comes out one way, and the second
     * element, nought, aborts it. Null where an argument is one this does not write.
     */
    private static String call(String name, Stdlib.Signature signature, Combinator rule,
                               Type.FnOf closure, String relation) {
        List<String> parameters = new ArrayList<>();
        for (int at = 0; at < closure.params().size(); at++) {
            parameters.add("p" + at);
        }
        List<String> arguments = new ArrayList<>();
        for (int at = 0; at < signature.params().size(); at++) {
            if (at == rule.closureArg()) {
                arguments.add("(" + String.join(", ", parameters) + ") -> Int.floorMod(1, p"
                        + rule.elementParam() + ") " + relation + " 0");
            } else if (at == rule.containerArg()) {
                String container = switch (signature.params().get(at)) {
                    case Type.ListOf _ -> "[1, 0]";
                    case Type.SetOf _ -> "Set.fromList([1, 0])";
                    case Type.MapOf _ -> "Map.fromList([(2, 1), (3, 0)])";
                    default -> null;
                };
                if (container == null) {
                    return null;
                }
                arguments.add(container);
            } else {
                return null;
            }
        }
        return """
                module demo

                data In = { n: Int }
                data Out = { n: Int }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = {
                    let applied = %s(%s)
                    Out { n = i.n }
                }
                """.formatted(name, String.join(", ", arguments));
    }

    /** Whether running {@code module} aborted. */
    private static boolean aborts(String module) throws Exception {
        Map<String, ClassFileImage> classes = Compiler.compile(module);
        ClassLoader loader = new ClassLoader(
                HowFarAnOperationAppliesItsClosureIsWhatTheLibraryComputesTest.class
                        .getClassLoader()) {
            @Override
            protected Class<?> findClass(String className) throws ClassNotFoundException {
                ClassFileImage image = classes.get(className);
                if (image == null) {
                    throw new ClassNotFoundException(className);
                }
                byte[] bytes = image.bytes();
                return defineClass(className, bytes, 0, bytes.length);
            }
        };
        @SuppressWarnings("unchecked")
        Decoder<Object, ?> decoder = (Decoder<Object, ?>) loader.loadClass("demo.In")
                .getMethod("decoder").invoke(null);
        Object in = ((Ok<?>) decoder.decode(Map.of("n", 0L), Path.ROOT)).value();
        @SuppressWarnings("unchecked")
        Behavior<Object, Object> behavior = (Behavior<Object, Object>)
                Emitted.behavior(loader, "demo", "run").getConstructor().newInstance();
        try {
            behavior.apply(in);
            return false;
        } catch (RuntimeException stopped) {
            for (Throwable cause = stopped; cause != null; cause = cause.getCause()) {
                if (cause instanceof ConstraintViolation) {
                    return true;
                }
            }
            throw stopped;
        }
    }
}
