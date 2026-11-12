package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A membership of a value the source wrote in a container made of another by operations that
 * keep, reorder or hold some of its elements draws the line of the value on the elements of the
 * input, and the line of what an operation kept them by — whichever operations they are, and
 * whichever stands outside.
 *
 * <p>The lines each is held to are worked out here from how the container is written, and not by
 * asking what a comparison of its elements draws: both could be told the same thing wrongly, and
 * a chain is where what one operation says of its elements is carried beneath another.
 */
class AMembershipInAChainOfOperationsDrawsTheLinesOfTheValueAndOfWhatWasKeptByTest {

    /** An operation on a container, written round {@code %s}, and the line it draws of its own. */
    private record Operation(String written, String line) {

        String around(String inner) {
            return written.formatted(inner);
        }
    }

    /** What leaves a container as it is, which is the end of a chain. */
    private static final Operation NOTHING = new Operation("%s", null);

    private static final List<Operation> OF_A_LIST = List.of(NOTHING,
            new Operation("List.filter(x -> x > 3, %s)", "l.nums[*] 3"),
            new Operation("List.take(2, %s)", null),
            new Operation("List.drop(1, %s)", null),
            new Operation("List.distinct(%s)", null),
            new Operation("List.sort(%s)", null),
            new Operation("List.reverse(%s)", null));

    private static final List<Operation> OF_A_MAP = List.of(NOTHING,
            new Operation("Map.filterEntries((_, v) -> v > 3, %s)", "l.rates[*] 3"),
            new Operation("Map.remove(\"Z\", %s)", null),
            new Operation("Map.intersection(%s, l.rates2)", null));

    /** What each behavior of the model is expected to draw, by its name. */
    private static final Map<String, Set<String>> EXPECTED = new TreeMap<>();

    private static final String MODEL = model();

    private static String model() {
        StringBuilder source = new StringBuilder("""
                module probe
                data Line = { nums: List<Int>, rates: Map<String, Int>, rates2: Map<String, Int> }
                """);
        for (Operation outer : OF_A_LIST) {
            for (Operation inner : OF_A_LIST) {
                add(source, "nums" + EXPECTED.size(), "Bool",
                        "List.contains(5, " + outer.around(inner.around("l.nums")) + ")",
                        lines("l.nums[*] 5", outer, inner));
            }
        }
        for (Operation outer : OF_A_MAP) {
            for (Operation inner : OF_A_MAP) {
                String map = outer.around(inner.around("l.rates"));
                add(source, "keys" + EXPECTED.size(), "Bool",
                        "List.contains(\"K\", Map.keys(" + map + "))",
                        lines("l.rates[key] K", outer, inner));
                add(source, "values" + EXPECTED.size(), "Bool",
                        "List.contains(5, Map.values(" + map + "))",
                        lines("l.rates[*] 5", outer, inner));
            }
        }
        return source.toString();
    }

    private static void add(StringBuilder source, String name, String type, String body,
                            Set<String> lines) {
        source.append("behavior ").append(name).append(" : (l: Line) -> ").append(type)
                .append("\nlet ").append(name).append(" (l) = ").append(body).append('\n');
        EXPECTED.put(name, lines);
    }

    private static Set<String> lines(String ofTheValue, Operation... chain) {
        Set<String> out = new TreeSet<>();
        out.add(ofTheValue);
        for (Operation each : chain) {
            if (each.line() != null) {
                out.add(each.line());
            }
        }
        return out;
    }

    @Test
    void theLinesAreThoseOfTheValueAndOfWhatWasKeptByWhateverTheChainIs() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                MODEL);
        Map<String, List<BorderAssessment>> read = Adequacy.readingsOf(compilation.db(), "probe");
        List<String> wrong = new ArrayList<>();
        EXPECTED.forEach((name, expected) -> {
            Set<String> drawn = new TreeSet<>();
            read.getOrDefault(name, List.of())
                    .forEach(each -> drawn.add(each.left() + " " + each.value()));
            if (!drawn.equals(expected)) {
                wrong.add(name + " drew " + drawn + " and not " + expected + ": "
                        + MODEL.lines().filter(line -> line.startsWith("let " + name + " "))
                                .findFirst().orElse(""));
            }
        });
        assertEquals(List.of(), wrong);
    }
}
