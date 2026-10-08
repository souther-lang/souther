package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every operation the library says holds something exactly when its source does, does.
 *
 * <p>The binder holds the statement to the signature only: that the source and the answer are
 * containers. Whether the answer is empty exactly where the source is, is what the definition says,
 * and this asks it — over every list of up to three elements drawn from minus one, nought and one,
 * each operation handed the shape that comes closest to emptying it: a mapping that sends every
 * element to one, and a list repeating what it holds.
 *
 * <p>Read off the declarations: an operation that says so and has no row here fails.
 */
class EveryOperationThatKeepsWhetherItHoldsAnythingDoesTest {

    /** For each operation, a behavior answering whether its answer holds anything, and whether
     *  what it was handed did. */
    private static final Map<String, String> RUN = new LinkedHashMap<>();

    static {
        RUN.put("Set.map", """
                Out { result = Bool.not(Set.isEmpty(Set.map(x -> 0, Set.fromList(xs)))),
                      source = Bool.not(Set.isEmpty(Set.fromList(xs))) }""");
        RUN.put("Set.fromList", """
                Out { result = Bool.not(Set.isEmpty(Set.fromList(List.append(xs, xs)))),
                      source = Bool.not(List.isEmpty(List.append(xs, xs))) }""");
    }

    @Test
    void everyOneIsRun() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        Set<String> declared = new TreeSet<>();
        for (ValueName operation : facts.keepsWhetherItHoldsAnything()) {
            declared.add(((ValueName.Stdlib) operation).qualified());
        }
        assertEquals(declared, new TreeSet<>(RUN.keySet()));
    }

    @Test
    void everyOneHoldsOfEverySmallList() throws Exception {
        StringBuilder module = new StringBuilder("""
                module demo

                data In = { xs: List<Int> }
                data Out = { result: Bool, source: Bool }
                """);
        List<String> names = new ArrayList<>();
        for (String each : RUN.values()) {
            String name = "keeps" + names.size();
            names.add(name);
            module.append("\nbehavior ").append(name).append(" : (i: In) -> Out constructs Out\n")
                    .append("let ").append(name).append(" (i) = { let xs = i.xs\n")
                    .append(each).append(" }\n");
        }
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(module.toString()),
                getClass().getClassLoader());
        List<String> broken = new ArrayList<>();
        int at = 0;
        for (String operation : RUN.keySet()) {
            Object behavior = Emitted.behavior(loader, "demo", names.get(at++))
                    .getConstructor().newInstance();
            for (List<Long> xs : smallLists()) {
                Object in = Codecs.decoded(loader, "demo.In", Map.of("xs", xs));
                Map<?, ?> out = (Map<?, ?>) Codecs.encode(loader, "demo.Out",
                        Codecs.apply(behavior, in));
                if (!out.get("result").equals(out.get("source"))) {
                    broken.add(operation + " over " + xs);
                }
            }
        }
        assertEquals(List.of(), broken);
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
