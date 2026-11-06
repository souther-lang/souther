package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison some run gets to is never one this compiler says no row arrives at, held against
 * the runs themselves.
 *
 * <p>Each body hands out elements of {@code x.items} through some way of writing a name, asks of
 * them a condition and its denial, and compares {@code x.gate} past them. Whether some run gets to
 * that comparison is found by running the compiled behavior on every list of no, one and two
 * elements whose values are the ones the condition tells apart — and not by anything the analysis
 * reads. Asked of two names, two elements meet the condition and its denial; asked of one, none
 * does, and there the analysis is free to say the comparison is reached by no row, which some of
 * them are held to so that the check says something.
 *
 * <p>The conditions are of each kind of value an element holds — a number, a truth, a string, and
 * a string an operation made of it — since each is a different place a statement holds which
 * value it is about.
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
     *  denial of the second, reaching the gate where both hold. */
    private record Shape(String name, String written) {}

    private static final String GATE = "(if x.gate > 0 then 100 else 100)";

    private static final List<Shape> SHAPES = List.of(
            new Shape("joined", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s &&"
                    + " Bool.not(%2$s) then " + GATE + " else 0, x.items)), x.items))"),
            new Shape("forks", "List.sum(List.map(a -> List.sum(List.map(b -> if %1$s then"
                    + " (if Bool.not(%2$s) then " + GATE + " else 0) else 0, x.items)),"
                    + " x.items))"),
            new Shape("fold", "List.sum(List.map(a -> if List.fold((acc, b) -> (acc && %1$s) ||"
                    + " (%1$s && Bool.not(%2$s)), false, x.items) then " + GATE + " else 0,"
                    + " x.items))"),
            new Shape("quantifier", "List.sum(List.map(a -> if List.any(b -> Bool.not(%2$s) &&"
                    + " %1$s, x.items) then " + GATE + " else 0, x.items))"));

    private static final String MODULE = "probe.oracle";

    private static final String DECLARED = """
            module probe.oracle

            data Item = { n: Int, paid: Bool, text: String }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10
            """;

    /** One body to measure: its behavior's name, its source and the kind it asks. */
    private record Body(String behavior, String written, Kind kind, boolean twoNames) {}

    @Test
    void aComparisonSomeRunReachesIsNeverSaidToHaveNoLine() throws Exception {
        List<Body> bodies = new ArrayList<>();
        for (Shape shape : SHAPES) {
            for (Kind kind : KINDS) {
                for (boolean twoNames : List.of(true, false)) {
                    bodies.add(new Body(shape.name() + "_" + kind.name() + "_"
                            + (twoNames ? "apart" : "alike"),
                            shape.written().formatted(kind.written().formatted("a"),
                                    kind.written().formatted(twoNames ? "b" : "a")),
                            kind, twoNames));
                }
            }
        }
        StringBuilder source = new StringBuilder(DECLARED);
        for (Body each : bodies) {
            source.append("""

                    behavior %s : (x: Input) -> Int
                    let %s (x) = %s
                    """.formatted(each.behavior(), each.behavior(), each.written()));
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
        Object behavior = Emitted.behavior(loader, MODULE, body.behavior()).getConstructor()
                .newInstance();
        for (List<Object> values : lists(body.kind().values())) {
            List<Map<String, Object>> items = new ArrayList<>();
            for (Object value : values) {
                Map<String, Object> item = new LinkedHashMap<>(
                        Map.of("n", 1L, "paid", false, "text", "b"));
                item.put(body.kind().field(), value);
                items.add(item);
            }
            Object out = Codecs.apply(behavior, Codecs.decoded(loader, MODULE + ".Input",
                    Map.of("items", items, "gate", 1L)));
            if (((Number) out).longValue() >= 100) {
                return true;
            }
        }
        return false;
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
