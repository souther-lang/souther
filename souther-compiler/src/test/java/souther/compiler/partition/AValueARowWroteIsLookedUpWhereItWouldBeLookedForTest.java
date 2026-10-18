package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.AnswerObservation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.AsACompilationAllows;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a row wrote at a path, looked up by the elements a walk chose, is what looking through
 * every value for the first reached through them finds; and the values under what a walk chose
 * beside one container are those looking through them all keeps.
 *
 * <p>Over every choice a walk can make of the containers a path is inside — an element of each,
 * none of some, an element a container does not have — and of containers the path is not inside,
 * on a row whose orders hold different numbers of lines.
 */
class AValueARowWroteIsLookedUpWhereItWouldBeLookedForTest {

    private static final String MODEL = """
            module g

            data Line = { sku: String, qty: Int }

            data Order = { lines: List<Line>, tags: List<String> }

            behavior decide : (orders: List<Order>) -> Int
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("lines");

    private static final TermPath TAGS = ORDERS.element().then("tags");

    @Test
    void everyChoiceIsLookedUpAsItWouldBeLookedFor() {
        StandingAtAPoint.RowWalk walk = new StandingAtAPoint.RowWalk(
                new BehaviorInputs(List.of("orders"), List.of(new Type.ListOf(named("Order"))),
                        RuleReadings.ofSource(MODEL), POLICY),
                new ObservedInputs(List.of(new ObservedValue.Sequence(List.of(
                        order(3, 2), order(1, 0), order(0, 1), order(4, 3)))),
                        new Generator.Watched.NoAccount(), new AnswerObservation.NotAnswered()));
        List<TermPath> paths = List.of(ORDERS, ORDERS.element(), LINES, LINES.element(),
                LINES.element().then("sku"), TAGS, TAGS.element());
        for (TermPath path : paths) {
            StandingAtAPoint.Written written = walk.at(path);
            List<BehaviorInputs.Occurrence> values = written.values();
            for (Map<TermPath, Integer> chosen : choices()) {
                assertEquals(firstUnder(values, chosen, null), written.under(chosen),
                        () -> path + " under " + chosen);
                for (TermPath container : path.containersHoldingIt()) {
                    assertEquals(allUnder(values, chosen, container),
                            written.besideOf(container, chosen),
                            () -> path + " beside " + container + " under " + chosen);
                }
            }
        }
    }

    /** Every choice of nothing or an element in each of the containers, one past the longest. */
    private static List<Map<TermPath, Integer>> choices() {
        List<Map<TermPath, Integer>> out = new ArrayList<>();
        out.add(Map.of());
        for (Map.Entry<TermPath, Integer> container : Map.of(ORDERS, 4, LINES, 4, TAGS, 3)
                .entrySet()) {
            List<Map<TermPath, Integer>> wider = new ArrayList<>(out);
            for (Map<TermPath, Integer> each : out) {
                for (int element = 0; element <= container.getValue(); element++) {
                    Map<TermPath, Integer> deeper = new HashMap<>(each);
                    deeper.put(container.getKey(), element);
                    wider.add(deeper);
                }
            }
            out = wider;
        }
        return out;
    }

    private static ObservedValue firstUnder(List<BehaviorInputs.Occurrence> values,
                                            Map<TermPath, Integer> chosen, TermPath apart) {
        List<BehaviorInputs.Occurrence> all = allUnder(values, chosen, apart);
        return all.isEmpty() ? null : all.getFirst().value();
    }

    /** Every value no container but {@code apart} was reached through another element of. */
    private static List<BehaviorInputs.Occurrence> allUnder(List<BehaviorInputs.Occurrence> values,
                                                            Map<TermPath, Integer> chosen,
                                                            TermPath apart) {
        List<BehaviorInputs.Occurrence> out = new ArrayList<>();
        for (BehaviorInputs.Occurrence each : values) {
            boolean agrees = true;
            for (Map.Entry<TermPath, Integer> picked : chosen.entrySet()) {
                Integer taken = each.at().elementAt(picked.getKey());
                if (!picked.getKey().equals(apart) && taken != null
                        && !taken.equals(picked.getValue())) {
                    agrees = false;
                }
            }
            if (agrees) {
                out.add(each);
            }
        }
        return out;
    }

    private static ObservedValue order(int lines, int tags) {
        List<ObservedValue> written = new ArrayList<>();
        for (int each = 0; each < lines; each++) {
            written.add(new ObservedValue.Constructed(sym("Line"), Map.of(
                    "sku", new ObservedValue.Text("s" + each % 2),
                    "qty", new ObservedValue.Integer(each))));
        }
        List<ObservedValue> tagged = new ArrayList<>();
        for (int each = 0; each < tags; each++) {
            tagged.add(new ObservedValue.Text("t" + each));
        }
        return new ObservedValue.Constructed(sym("Order"), Map.of(
                "lines", new ObservedValue.Sequence(written),
                "tags", new ObservedValue.Sequence(tagged)));
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
