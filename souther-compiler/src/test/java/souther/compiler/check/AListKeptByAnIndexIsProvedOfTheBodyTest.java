package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Rel;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Which elements of a list an operation keeps by their index — the ones before a count, or the
 * ones from it on — is proved of the body, side by side: the step puts the element where the
 * index stands to the count as the fact says, and keeps what it has where it does not.
 */
class AListKeptByAnIndexIsProvedOfTheBodyTest {

    private static final ValueName TAKE = ValueName.Stdlib.operation("List", "take");
    private static final ValueName DROP = ValueName.Stdlib.operation("List", "drop");

    private static final String SHIPPED_TAKE = "if i < n then (next, ys ++ [x]) else (next, ys)";
    private static final String SHIPPED_DROP = "if i >= n then (next, ys ++ [x]) else (next, ys)";

    /** Control: what the library ships is proved, each with the side it keeps. */
    @Test
    void theLibraryAsShippedKeepsWhatItIsSaidTo() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        assertEquals(Rel.LT, facts.holdsTheElementsByIndex(TAKE).kept());
        assertEquals(Rel.GE, facts.holdsTheElementsByIndex(DROP).kept());
        assertEquals(List.of(), unproved(facts), "nothing kept by an index is left open");
    }

    /** Control for the bodies below: the facts alone, over the library as shipped, are proved. */
    @Test
    void theFactsAloneAreProvedOfTheBodiesAsShipped() {
        assertEquals(List.of(), unproved(proved(SHIPPED_TAKE, SHIPPED_TAKE, byIndex())));
    }

    /** A take whose step keeps one element more is not a take of the elements before the count. */
    @Test
    void aStepThatKeepsTheElementAtTheCountIsNoTake() {
        assertEquals(List.of(TAKE), unproved(proved(SHIPPED_TAKE,
                "if i <= n then (next, ys ++ [x]) else (next, ys)", byIndex())));
    }

    /** And a drop whose step leaves out the element at the count is no drop from it. */
    @Test
    void aStepThatLeavesOutTheElementAtTheCountIsNoDrop() {
        assertEquals(List.of(DROP), unproved(proved(SHIPPED_DROP,
                "if i > n then (next, ys ++ [x]) else (next, ys)", byIndex())));
    }

    /** The side is part of what is proved: a take said to keep the elements from the count on is
     *  not proved of the body that keeps the ones before it. */
    @Test
    void theOtherSideIsNotProved() {
        List<OperationFacts.Declared> swapped = new ArrayList<>();
        for (OperationFacts.Declared each : byIndex()) {
            swapped.add(each.fact() instanceof OperationFact.HoldsTheElementsByIndex kept
                    ? new OperationFacts.Declared(each.operation(),
                            new OperationFact.HoldsTheElementsByIndex(kept.count(), kept.list(),
                                    kept.kept().denied()))
                    : each);
        }
        assertEquals(List.of(TAKE, DROP), unproved(proved(SHIPPED_TAKE, SHIPPED_TAKE, swapped)));
    }

    /** Only the two sides of an index are a side: an element at the count alone is no run of the
     *  list. */
    @Test
    void aRelationThatIsNoSideIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> new OperationFact.HoldsTheElementsByIndex(new ArgumentRef.At(0),
                        new ArgumentRef.At(1), Rel.EQ));
    }

    /** The operations kept by an index that are stated and not proved, in the order stated. */
    private static List<ValueName> unproved(BoundOperationFacts facts) {
        return facts.notProvedOfTheirBodies().stream()
                .filter(each -> each instanceof BoundOperationFact.HoldsTheElementsByIndex)
                .<ValueName>map(each -> each.operation().operation())
                .toList();
    }

    /** The library as shipped with {@code shipped} written as {@code body}, {@code facts} proved
     *  of it. */
    private static BoundOperationFacts proved(String shipped, String body,
                                              List<OperationFacts.Declared> facts) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(shipped)
                ? text.replace(shipped, body) : text);
        return OperationFactBinder.bindAll(stdlib, facts);
    }

    /** What the language declares of a list kept by an index, and nothing else. */
    private static List<OperationFacts.Declared> byIndex() {
        return OperationFacts.declarations().stream()
                .filter(each -> each.fact() instanceof OperationFact.HoldsTheElementsByIndex)
                .toList();
    }
}
