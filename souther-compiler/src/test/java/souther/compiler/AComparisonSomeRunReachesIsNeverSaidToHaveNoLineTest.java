package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.lang.classfile.ClassFile;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDescs;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison some run gets to is never one this compiler says no row arrives at, held against
 * the runs themselves.
 *
 * <p>Each body hands out elements of a list through some way of writing a name, asks of them a
 * condition and its denial, and compares {@code x.gate} past them. Whether some run gets to that
 * comparison is found by running the compiled behavior on every list of no, one and two elements
 * whose values are the ones the condition tells apart — and not by anything the analysis reads.
 * Asked of two names, two elements meet the condition and its denial; asked of one, none does, and
 * there the analysis is free to say the comparison is reached by no row, which some of them are
 * held to so that the check says something.
 *
 * <p>The conditions are of each kind of value an element holds — a number, a truth, a string, and
 * a string an operation made of it — since each is a different place a statement holds which
 * value it is about. The list is the input's, or one a dependency answered, since a place inside
 * an answer is said in words of its own.
 */
class AComparisonSomeRunReachesIsNeverSaidToHaveNoLineTest {

    /** A condition, written of one name, and the values of the element field it tells apart. */
    private record Kind(String name, String written, String field, List<Object> values) {}

    private static final List<Kind> KINDS = List.of(
            new Kind("number", "%s.n < 0", "n", List.of(-1L, 0L)),
            new Kind("truth", "%s.paid", "paid", List.of(false, true)),
            new Kind("string", "String.startsWith(\"X\", %s.text)", "text", List.of("Xa", "b")),
            new Kind("made", "String.startsWith(\"X\", String.uppercase(%s.text))", "text",
                    List.of("xa", "b")));

    /** A way of writing two names, {@code %1$s} the condition of the first and {@code %2$s} its
     *  denial of the second, over the list {@code ITEMS}, reaching the gate where both hold.
     *  {@code %3$s} and {@code %4$s} are the two names themselves, for a shape that weighs their
     *  numbers against each other in one comparison and so is of numbers alone. */
    private record Shape(String name, String written, boolean ofNumbers) {

        Shape(String name, String written) {
            this(name, written, false);
        }
    }

    private static final String GATE = "(if x.gate > 0 then 100 else 100)";

    private static final List<Shape> SHAPES = List.of(
            new Shape("joined", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0, ITEMS)), ITEMS))"),
            new Shape("forks", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s then"
                    + " (if Bool.not(%2$s) then " + GATE + " else 0) else 0, ITEMS)),"
                    + " ITEMS))"),
            new Shape("fold", "List.sum(List.map(a -> if List.fold((acc, b) -> (acc && %1$s) ||"
                    + " (%1$s && Bool.not(%2$s)), false, ITEMS) then " + GATE + " else 0,"
                    + " ITEMS))"),
            new Shape("quantifier", "List.sum(List.map(a -> if List.any(b -> Bool.not(%2$s) &&"
                    + " %1$s, ITEMS) then " + GATE + " else 0, ITEMS))"),
            // The same two closures over what an operation made of the list and holds its
            // elements in: their order turned, or some of them kept, on one side or both.
            new Shape("reversed", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0, List.reverse(ITEMS))),"
                    + " List.reverse(ITEMS)))"),
            new Shape("filtered", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0, List.filter(e -> e.n > -5,"
                    + " ITEMS))), List.filter(e -> e.n > -5, ITEMS)))"),
            new Shape("reversedOnce", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0, ITEMS)),"
                    + " List.reverse(ITEMS)))"),
            // Two entries a lookup took out of a map filed from the list, one name each.
            new Shape("lookedUp", "(match Map.get(0, List.indexBy(.id, ITEMS)) with | Some a ->"
                    + " (match Map.get(1, List.indexBy(.id, ITEMS)) with | Some b -> (if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0) | None -> 0) | None -> 0)"),
            // Two numbers of two elements in one difference, which is no number where they are
            // taken for one, over the list and what an operation made of it.
            new Shape("difference", "List.sum(List.map(a -> List.sum(List.map(b -> if %3$s.n -"
                    + " %4$s.n > 0 then " + GATE + " else 0, ITEMS)), List.reverse(ITEMS)))",
                    true));

    /** Where the list is: written as {@code ITEMS} is replaced, and whether a dependency answers
     *  it. */
    private record Source(String name, String written, boolean answered) {}

    private static final List<Source> SOURCES = List.of(
            new Source("input", "x.items", false),
            new Source("answer", "readItems(x)", true));

    private static final String MODULE = "probe.oracle";

    private static final String DECLARED = """
            module probe.oracle

            data Item = { id: Int, n: Int, paid: Bool, text: String }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10
            behavior readItems : (x: Input) -> List<Item>
            """;

    /** One body to measure: its behavior's name, its source and the kind it asks. */
    private record Body(String behavior, String written, Kind kind, boolean twoNames,
                        Source source) {}

    @Test
    void aComparisonSomeRunReachesIsNeverSaidToHaveNoLine() throws Exception {
        List<Body> bodies = new ArrayList<>();
        for (Source source : SOURCES) {
            for (Shape shape : SHAPES) {
                for (Kind kind : KINDS) {
                    if (shape.ofNumbers() && !kind.field().equals("n")) {
                        continue;
                    }
                    for (boolean twoNames : List.of(true, false)) {
                        String second = twoNames ? "b" : "a";
                        bodies.add(new Body(source.name() + "_" + shape.name() + "_"
                                + kind.name() + "_" + (twoNames ? "apart" : "alike"),
                                shape.written().replace("ITEMS", source.written()).formatted(
                                        kind.written().formatted("a"),
                                        kind.written().formatted(second), "a", second),
                                kind, twoNames, source));
                    }
                }
            }
        }
        StringBuilder source = new StringBuilder(DECLARED);
        for (Body each : bodies) {
            source.append(each.source().answered() ? """

                    behavior %1$s : (x: Input) -> Int
                        depends on readItems
                    let %1$s (x, readItems) = %2$s
                    """.formatted(each.behavior(), each.written()) : """

                    behavior %1$s : (x: Input) -> Int
                    let %1$s (x) = %2$s
                    """.formatted(each.behavior(), each.written()));
        }
        Map<String, Boolean> noLine = noLineAtTheGate(source.toString());
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(source.toString()),
                getClass().getClassLoader());
        List<String> wrong = new ArrayList<>();
        List<String> unrun = new ArrayList<>();
        int closed = 0;
        for (Body each : bodies) {
            boolean reached = reachedOnSomeRun(loader, each);
            if (each.twoNames() && !reached) {
                unrun.add(each.behavior());
            }
            if (reached && noLine.get(each.behavior())) {
                wrong.add(each.behavior() + ": " + each.written());
            }
            if (!reached && noLine.get(each.behavior())) {
                closed++;
            }
        }
        assertEquals(List.of(), unrun, "two elements meet a condition and its denial, and the"
                + " lists run here hold two such elements");
        assertEquals(List.of(), wrong, "a comparison some run gets to, said to have no line");
        assertTrue(closed > 0, "no body no run gets to the gate in was said to be so");
    }

    /** Whether some list of no, one or two elements of the values {@code body}'s condition
     *  tells apart gets a run of it to the gate. */
    private static boolean reachedOnSomeRun(BytesClassLoader loader, Body body)
            throws Exception {
        for (List<Object> values : lists(body.kind().values())) {
            List<Map<String, Object>> items = new ArrayList<>();
            for (Object value : values) {
                Map<String, Object> item = new LinkedHashMap<>(Map.of("id",
                        (long) items.size(), "n", 1L, "paid", false, "text", "b"));
                item.put(body.kind().field(), value);
                items.add(item);
            }
            Object out = Codecs.apply(behavior(loader, body), Codecs.decoded(loader,
                    MODULE + ".Input", Map.of("items", items, "gate", 1L)));
            if (((Number) out).longValue() >= 100) {
                return true;
            }
        }
        return false;
    }

    /** {@code body}'s behavior, handed a dependency that answers the input's list where it asks
     *  one. */
    private static Object behavior(BytesClassLoader loader, Body body) throws Exception {
        if (!body.source().answered()) {
            return Emitted.behavior(loader, MODULE, body.behavior()).getConstructor()
                    .newInstance();
        }
        Class<?> asked = Emitted.behaviorInterface(loader, MODULE, "readItems");
        return Emitted.behaviorInterface(loader, MODULE, body.behavior())
                .getMethod("bind", asked).invoke(null, answering(asked, input -> {
                    try {
                        return input.getClass().getMethod("items").invoke(input);
                    } catch (ReflectiveOperationException e) {
                        throw new IllegalStateException(e);
                    }
                }));
    }

    /**
     * An implementation of the abstract base {@code base} an injected behavior is emitted as, whose
     * every {@code apply} answers what {@code answer} makes of its argument: what a Java author
     * would write, built here since a base is a class and no proxy can stand for one.
     */
    private static Object answering(Class<?> base, Function<Object, Object> answer)
            throws Exception {
        ClassDesc self = ClassDesc.of(base.getPackageName() + ".AnsweredHere");
        ClassDesc of = ClassDesc.of(base.getName());
        ClassDesc function = ClassDesc.of(Function.class.getName());
        byte[] bytes = ClassFile.of().build(self, cb -> {
            cb.withSuperclass(of).withFlags(ClassFile.ACC_PUBLIC);
            cb.withField("answer", function, ClassFile.ACC_PUBLIC | ClassFile.ACC_STATIC);
            cb.withMethodBody("<init>", MethodTypeDesc.of(ConstantDescs.CD_void),
                    ClassFile.ACC_PUBLIC, code -> code.aload(0)
                            .invokespecial(of, "<init>", MethodTypeDesc.of(ConstantDescs.CD_void))
                            .return_());
            for (Method each : base.getMethods()) {
                if (!each.getName().equals("apply") || each.getParameterCount() != 1
                        || !Modifier.isAbstract(each.getModifiers())) {
                    continue;
                }
                MethodTypeDesc type = MethodTypeDesc.of(
                        ClassDesc.ofDescriptor(each.getReturnType().descriptorString()),
                        ClassDesc.ofDescriptor(each.getParameterTypes()[0].descriptorString()));
                cb.withMethodBody("apply", type, ClassFile.ACC_PUBLIC, code -> code
                        .getstatic(self, "answer", function)
                        .aload(1)
                        .invokeinterface(function, "apply", MethodTypeDesc.of(
                                ConstantDescs.CD_Object, ConstantDescs.CD_Object))
                        .checkcast(type.returnType())
                        .areturn());
            }
        });
        Class<?> made = new Defining(base.getClassLoader()).defined(bytes);
        made.getField("answer").set(null, answer);
        return made.getConstructor().newInstance();
    }

    /** A loader of one class, under the one that loaded what it extends. */
    private static final class Defining extends ClassLoader {

        Defining(ClassLoader parent) {
            super(parent);
        }

        Class<?> defined(byte[] bytes) {
            return defineClass(null, bytes, 0, bytes.length);
        }
    }

    /** Every list of no, one and two of {@code values}. */
    private static List<List<Object>> lists(List<Object> values) {
        List<List<Object>> out = new ArrayList<>();
        out.add(List.of());
        for (Object one : values) {
            out.add(List.of(one));
            for (Object other : values) {
                out.add(List.of(one, other));
            }
        }
        return out;
    }

    /** For each behavior, whether the comparison on the gate was said to have no line. */
    private static Map<String, Boolean> noLineAtTheGate(String source) {
        Compilation made = Compilation.ofSource(source, "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        Map<String, Boolean> out = new LinkedHashMap<>();
        AdequacyReport.of(made).modules().getFirst().behaviors().forEach(behavior -> {
            Set<String> without = behavior.partition().notRead().stream()
                    .filter(PartitionEvidence.NotRead.ARule.class::isInstance)
                    .map(PartitionEvidence.NotRead::at)
                    .collect(Collectors.toUnmodifiableSet());
            out.put(behavior.name(), without.contains("x.gate"));
        });
        return out;
    }
}
