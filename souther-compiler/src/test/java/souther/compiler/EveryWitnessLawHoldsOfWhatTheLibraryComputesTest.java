package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementWitness;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every witness law the library declares holds of what the library computes.
 *
 * <p>A law is an equivalence a reader carries a statement across, and a binder holds it to the
 * signature only: that each side named is a side the value has. Whether the result really comes out
 * that way exactly where some element's answer does is what the operation's definition says, and
 * this asks the definition. Each operation is run over every list of up to three elements drawn from
 * minus one, nought and one, and the side of its result the law is about is held against the same
 * side of what its closure answered for each element.
 *
 * <p>Read off the declarations: an operation given a law and no row here fails, so a law is not
 * declared without being run.
 */
class EveryWitnessLawHoldsOfWhatTheLibraryComputesTest {

    /**
     * For each operation with a law, a behavior answering the side of the result the law is about
     * as {@code result} and the side of the closure's answer, element by element, as {@code each}.
     */
    private static final Map<String, String> RUN = new LinkedHashMap<>();

    static {
        RUN.put("List.filter", """
                Out { result = Bool.not(List.isEmpty(List.filter(x -> x > 0, xs))),
                      each = List.map(x -> x > 0, xs) }""");
        RUN.put("Set.filter", """
                Out { result = Bool.not(Set.isEmpty(Set.filter(x -> x > 0, Set.fromList(xs)))),
                      each = List.map(x -> x > 0, Set.toList(Set.fromList(xs))) }""");
        RUN.put("Map.filterEntries", """
                Out { result = Bool.not(Map.isEmpty(Map.filterEntries((k, v) -> v > 0,
                          Map.fromList(List.mapIndexed((i, x) -> (i, x), xs))))),
                      each = List.map(x -> x > 0, xs) }""");
        RUN.put("List.filterMap", """
                Out { result = Bool.not(List.isEmpty(List.filterMap(
                          x -> List.find(y -> y > 0, [x]), xs))),
                      each = List.map(x -> Option.withDefault(false,
                          Option.map(v -> true, List.find(y -> y > 0, [x]))), xs) }""");
        RUN.put("List.find", """
                Out { result = Option.withDefault(false,
                          Option.map(v -> true, List.find(x -> x > 0, xs))),
                      each = List.map(x -> x > 0, xs) }""");
        RUN.put("List.flatMap", """
                Out { result = Bool.not(List.isEmpty(List.flatMap(
                          x -> if x > 0 then [x, x] else [], xs))),
                      each = List.map(x -> Bool.not(List.isEmpty(
                          if x > 0 then [x, x] else [])), xs) }""");
        RUN.put("List.any", """
                Out { result = List.any(x -> x > 0, xs), each = List.map(x -> x > 0, xs) }""");
        RUN.put("List.all", """
                Out { result = List.all(x -> x > 0, xs), each = List.map(x -> x > 0, xs) }""");
    }

    @Test
    void everyLawIsRun() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Set<String> declared = new TreeSet<>();
        for (ValueName operation : facts.resultHasAnElementWitness()) {
            declared.add(((ValueName.Stdlib) operation).qualified());
        }
        assertEquals(declared, new TreeSet<>(RUN.keySet()));
    }

    @Test
    void everyLawHoldsOfEverySmallList() throws Exception {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        StringBuilder module = new StringBuilder("""
                module demo

                data In = { xs: List<Int> }
                data Out = { result: Bool, each: List<Bool> }
                """);
        List<String> names = new ArrayList<>();
        for (Map.Entry<String, String> each : RUN.entrySet()) {
            String name = "law" + names.size();
            names.add(name);
            module.append("\nbehavior ").append(name).append(" : (i: In) -> Out constructs Out\n")
                    .append("let ").append(name).append(" (i) = { let xs = i.xs\n")
                    .append(each.getValue()).append(" }\n");
        }
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module.toString()),
                getClass().getClassLoader());
        List<String> broken = new ArrayList<>();
        int at = 0;
        for (String operation : RUN.keySet()) {
            ElementWitness law = facts.resultHasAnElementWitness(
                    ValueName.Stdlib.operation(operation.substring(0, operation.indexOf('.')),
                            operation.substring(operation.indexOf('.') + 1)));
            Object behavior = Emitted.behavior(loader, "demo", names.get(at++))
                    .getConstructor().newInstance();
            for (List<Long> xs : smallLists()) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("xs", xs));
                Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                        Codecs.apply(behavior, in));
                if (!holds(law, (Boolean) out.get("result"), (List<?>) out.get("each"))) {
                    broken.add(operation + " over " + xs);
                }
            }
        }
        assertEquals(List.of(), broken);
    }

    /** Whether the result came out the law's way exactly where some element's answer did. */
    private static boolean holds(ElementWitness law, boolean result,
                                 List<?> each) {
        SideAnswered witness = law.ofTheClosure();
        boolean someWitness = each.stream().anyMatch(answer -> answer.equals(witness.holds()));
        return (result == law.result().holds()) == someWitness;
    }

    private static List<List<Long>> smallLists() {
        List<List<Long>> out = new ArrayList<>();
        out.add(List.of());
        List<List<Long>> last = List.of(List.of());
        for (int size = 1; size <= 3; size++) {
            List<List<Long>> next = new ArrayList<>();
            for (List<Long> shorter : last) {
                for (long value = -1; value <= 1; value++) {
                    List<Long> longer = new ArrayList<>(shorter);
                    longer.add(value);
                    next.add(List.copyOf(longer));
                }
            }
            out.addAll(next);
            last = next;
        }
        return out;
    }
}
