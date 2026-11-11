package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A container asked for a member the source wrote is asked of its elements what a comparison of
 * them with that value is: the line is at the value, and a row at it holds the value in the
 * container, a row beside it holds another. A member that is another place of the row is a
 * relation of two values and draws none.
 */
class AContainerAskedForAWrittenMemberDrawsTheLineAComparisonWithItDrawsTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module probe
            data Line = { code: String, rates: Map<String, Int>, tags: List<String>,
                          ids: Set<String>, nums: List<Int> }

            behavior any : (l: Line) -> Bool
            let any (l) = List.any(t -> t == "K", l.tags)

            behavior listed : (l: Line) -> Bool
            let listed (l) = List.contains("K", l.tags)

            behavior setted : (l: Line) -> Bool
            let setted (l) = Set.contains("K", l.ids)

            behavior keyed : (l: Line) -> Bool
            let keyed (l) = Map.containsKey("USD", l.rates)

            behavior absent : (l: Line) -> Bool
            let absent (l) = Bool.not(List.contains("K", l.tags))

            behavior guarded : (l: Line) -> Int
            let guarded (l) = if Map.containsKey("USD", l.rates) then 1 else 0

            behavior numbered : (l: Line) -> Bool
            let numbered (l) = List.contains(5, l.nums)

            behavior another : (l: Line) -> Bool
            let another (l) = Map.containsKey(l.code, l.rates)
            """;

    /** What a comparison of the elements draws is what holding the value in a list, a set or a
     *  map's keys draws, however the statement is written. */
    @Test
    void holdingTheValueDrawsTheLineComparingTheElementsWithItDraws() {
        assertEquals(Set.of("l.tags[*] K"), linesOf("any"));
        assertEquals(linesOf("any"), linesOf("listed"));
        assertEquals(linesOf("any"), linesOf("absent"));
        assertEquals(Set.of("l.ids[*] K"), linesOf("setted"));
        assertEquals(Set.of("l.rates[key] USD"), linesOf("keyed"));
        assertEquals(linesOf("keyed"), linesOf("guarded"));
        assertEquals(Set.of("l.nums[*] 5"), linesOf("numbered"));
    }

    /** A row at the line holds the value, and a row on either side holds another: the rows are
     *  read back. */
    @Test
    void theRowsAreAtTheValueAndEitherSideOfIt() {
        List<String> at = new ArrayList<>();
        List<String> either = new ArrayList<>();
        for (String name : List.of("listed", "setted", "keyed", "absent", "numbered")) {
            for (BorderAssessment border : borders(name)) {
                for (Map.Entry<?, ItemAssessment> item : border.items().entrySet()) {
                    String row = certified(item.getValue());
                    if (row == null) {
                        continue;
                    }
                    (item.getKey().toString().startsWith("AtTheLine") ? at : either).add(row);
                }
            }
        }
        assertEquals(5, at.size(), at.toString());
        assertTrue(at.get(0).contains("tags = [\"K\"]"), at.toString());
        assertTrue(at.get(1).contains("ids = [\"K\"]"), at.toString());
        assertTrue(at.get(2).contains("rates = [(\"USD\", 0)]"), at.toString());
        assertTrue(at.get(3).contains("tags = [\"K\"]"), at.toString());
        assertTrue(at.get(4).contains("nums = [5]"), at.toString());
        assertTrue(either.stream().noneMatch(row -> row.contains("\"K\"")
                || row.contains("\"USD\"") || row.contains("nums = [5]")), either.toString());
        assertTrue(either.stream().anyMatch(row -> row.contains("nums = [4]")), either.toString());
        assertTrue(either.stream().anyMatch(row -> row.contains("nums = [6]")), either.toString());
    }

    /** The member being another place of the row relates two values and divides neither. */
    @Test
    void aMemberThatIsAnotherPlaceDrawsNoLine() {
        assertEquals(Set.of(), linesOf("another"));
    }

    private static Set<String> linesOf(String behavior) {
        Set<String> out = new TreeSet<>();
        borders(behavior).forEach(each -> out.add(each.left() + " " + each.value()));
        return out;
    }

    private static List<BorderAssessment> borders(String behavior) {
        List<BorderAssessment> lines = Adequacy.readingsOf(measured().db(), "probe").get(behavior);
        return lines == null ? List.of() : lines;
    }

    private static String certified(ItemAssessment item) {
        if (!(item instanceof ItemAssessment.Owed owed)) {
            return null;
        }
        for (ItemAssessment.Attempt attempt : owed.searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Certified row) {
                return row.row().inputs().stream().map(each -> each.text()).toList().toString();
            }
        }
        return null;
    }

    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured() {
        return MEASURED.computeIfAbsent(MODEL, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), source);
            return compilation;
        });
    }
}
