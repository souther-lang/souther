package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation answers the entries of a map where a closure holds of the key and the value is
 * a statement of the entries and not of the values, and is proved of the body: each entry kept is
 * put whole, that key with that value, where the closure holds of them and none is where it does
 * not. A body that keeps the entries the closure fails, or keeps either way, or whose put does not
 * say which key the value is filed under, is none of it.
 */
class TheEntriesAMapFilterKeepsAreProvedOfTheBodyAsKeyAndValueTest {

    private static final ValueName FILTER_ENTRIES =
            ValueName.Stdlib.operation("Map", "filterEntries");
    private static final ValueName MAP_INSERT = ValueName.Stdlib.operation("Map", "insert");
    private static final ValueName LIST_FILTER = ValueName.Stdlib.operation("List", "filter");

    private static final String SHIPPED = "Map.fold((acc, k, v) -> if keep(k, v) then "
            + "Map.insert(k, v, acc) else acc, Map.empty, m)";

    /** Control: the library as shipped keeps the entries where it is said to, and says nothing of
     *  its values being kept as elements are. */
    @Test
    void aMapFilterIsProvedToKeepTheEntriesWhereTheClosureHolds() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertNotNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertNull(facts.keepsWhereItHolds(FILTER_ENTRIES),
                "a closure of a key and a value is no statement of the values");
        assertEquals(List.of(), unproved(facts), "nothing stated of it is left open");
    }

    /** A step keeping the entry where the closure fails is not a filter. */
    @Test
    void aStepKeepingTheEntryWhereTheClosureFailsIsNoFilter() {
        BoundOperationFacts facts = proved("Map.fold((acc, k, v) -> if keep(k, v) then acc "
                + "else Map.insert(k, v, acc), Map.empty, m)");

        assertNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertEquals(List.of(FILTER_ENTRIES), unproved(facts), "stated, and left unproved");
    }

    /** Putting the entry in on both ways is keeping it whatever the closure answers. */
    @Test
    void aStepKeepingTheEntryEitherWayIsNoFilter() {
        assertNull(proved("Map.fold((acc, k, v) -> if keep(k, v) then Map.insert(k, v, acc) "
                + "else Map.insert(k, v, acc), Map.empty, m)")
                .keepsEntriesWhereItHolds(FILTER_ENTRIES));
    }

    /** A walk started from the map itself keeps every entry, whether or not the closure holds. */
    @Test
    void aWalkNotStartedFromNothingIsNoFilter() {
        assertNull(proved("Map.fold((acc, k, v) -> if keep(k, v) then Map.insert(k, v, acc) "
                + "else acc, m, m)").keepsEntriesWhereItHolds(FILTER_ENTRIES));
    }

    /** A put that does not say which key it files the value under keeps no entry: the value is one
     *  of the source's, and the answer may hold it under any key. */
    @Test
    void aPutThatSaysNoKeyKeepsNoEntry() {
        List<OperationFacts.Declared> declared = new ArrayList<>();
        declared.add(new OperationFacts.Declared(MAP_INSERT, new OperationFact.PutsAValueIn(
                new ArgumentRef.At(1), new ArgumentRef.At(2), Optional.empty())));
        declared.add(new OperationFacts.Declared(FILTER_ENTRIES,
                new OperationFact.KeepsTheEntriesWhereItHolds(new ArgumentRef.TheContainer())));

        BoundOperationFacts facts = OperationFactBinder.bindAll(DefaultStdlib.get(), declared);

        assertNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertEquals(List.of(FILTER_ENTRIES), unproved(facts), "stated, and left unproved");
    }

    /** Said of an operation whose closure is handed one element and no key, it is refused. */
    @Test
    void anOperationHandingItsClosureNoKeyKeepsNoEntries() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), List.of(
                        new OperationFacts.Declared(LIST_FILTER,
                                new OperationFact.KeepsTheEntriesWhereItHolds(
                                        new ArgumentRef.TheContainer())))));
        assertTrue(e.getMessage().contains("List.filter"), e.getMessage());
    }

    /** The operations it was stated of and not proved. */
    private static List<ValueName> unproved(BoundOperationFacts facts) {
        return facts.notProvedOfTheirBodies().stream()
                .filter(each -> each instanceof BoundOperationFact.KeepsTheEntriesWhereItHolds)
                .map(each -> each.operation().operation())
                .toList();
    }

    /** The library with {@code Map.filterEntries}'s body written as {@code body}, what is kept
     *  proved. */
    private static BoundOperationFacts proved(String body) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(SHIPPED)
                ? text.replace(SHIPPED, body) : text);
        return OperationFactBinder.bindAll(stdlib, OperationFacts.declarations().stream()
                .filter(each -> each.fact() instanceof OperationFact.KeepsTheEntriesWhereItHolds
                        || each.fact() instanceof OperationFact.PutsAValueIn)
                .toList());
    }
}
