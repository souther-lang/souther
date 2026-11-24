package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rewrite of what a map holds comes back as the map it was: the entry whose value was rewritten
 * has the same key and the rest are what they were, one result for each entry rewritten.
 */
class AMapIsRebuiltAroundTheValueARewriteChangedTest {

    private static final String MODEL = """
            module g

            data Row = { sku: String, qty: Int }

            data Snap = { byDay: Map<String, List<Row>> }

            behavior decide : (snap: Snap) -> Snap
            """;

    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            souther.compiler.values.AsACompilationAllows.admittedValues(),
            souther.compiler.values.AsACompilationAllows.whatARuleLeaves());

    private static final List<TermPath.Step> THE_LISTS = List.of(
            new TermPath.Step.Field("byDay"), new TermPath.Step.Element());

    private static final ObservedValue DAY_ONE = text("day-1");

    private static final ObservedValue DAY_TWO = text("day-2");

    @Test
    void theKeysAndTheOtherEntriesStayWhereTheyWere() {
        ObservedValue snap = snap(entry(DAY_ONE, row("A", 9)), entry(DAY_TWO, row("Z", 0)));
        ObservedValue before = snap(entry(DAY_ONE, row("A", 9)), entry(DAY_TWO, row("Z", 0)));

        List<ObservedValue> rewritten = rewriting(snap).toList();

        assertEquals(List.of(
                snap(entry(DAY_ONE, row("A", 9), row("A", 9)), entry(DAY_TWO, row("Z", 0))),
                snap(entry(DAY_ONE, row("A", 9)), entry(DAY_TWO, row("Z", 0), row("Z", 0)))),
                rewritten, "one result for each entry, and in each the other entry as it was");
        assertEquals(before, snap, "and the value rewritten is not changed");
    }

    @Test
    void aKeyIsNotTakenFromAnElementOfItsList() {
        ObservedValue snap = snap(entry(DAY_ONE, row("A", 9)));

        ObservedValue.Mapping rewritten = (ObservedValue.Mapping) ((ObservedValue.Constructed)
                rewriting(snap).findFirst().orElseThrow()).field("byDay");

        assertEquals(DAY_ONE, rewritten.entries().getFirst().key(),
                "the entry is filed under the key it had, whatever its elements hold");
    }

    @Test
    void aMapHoldingNothingHasNoValueToRewrite() {
        assertEquals(List.of(), rewriting(snap()).toList());
    }

    private static Stream<ObservedValue> rewriting(ObservedValue snap) {
        BehaviorInputs where = new BehaviorInputs(List.of("snap"), List.of(named("Snap")),
                RuleReadings.ofSource(MODEL), POLICY);
        return where.rewritingBelow(snap, named("Snap"), THE_LISTS,
                (here, _, _) -> Stream.of(repeatedFirst((ObservedValue.Sequence) here)),
                where.cachedViews());
    }

    /** The list with its first element held again after it. */
    private static ObservedValue repeatedFirst(ObservedValue.Sequence list) {
        List<ObservedValue> elements = new ArrayList<>(list.elements());
        elements.add(1, elements.getFirst());
        return new ObservedValue.Sequence(elements);
    }

    private static ObservedValue snap(ObservedValue.Entry... entries) {
        return new ObservedValue.Constructed(sym("Snap"),
                Map.of("byDay", new ObservedValue.Mapping(List.of(entries))));
    }

    private static ObservedValue.Entry entry(ObservedValue key, ObservedValue... rows) {
        return new ObservedValue.Entry(key, new ObservedValue.Sequence(List.of(rows)));
    }

    private static ObservedValue row(String sku, int qty) {
        return new ObservedValue.Constructed(sym("Row"),
                Map.of("sku", text(sku), "qty", new ObservedValue.Integer(qty)));
    }

    private static ObservedValue text(String value) {
        return new ObservedValue.Text(value);
    }

    private static Type named(String data) {
        return Type.ref(sym(data));
    }

    private static TypeSymbol sym(String data) {
        return TypeSymbols.declared(new TypeKey("g", data));
    }
}
