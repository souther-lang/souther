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

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * That an operation answers the elements of its argument where a closure holds of them, and no
 * other, is said of the elements and not of their order, and proved of the body: a list put
 * together in the order of its source and a set put by what it holds are one statement, and a body
 * that keeps where the closure fails, or keeps either way, is neither.
 */
class TheElementsAFilterKeepsAreProvedOfTheBodyWhateverItKeepsThemInTest {

    private static final ValueName LIST_FILTER = ValueName.Stdlib.operation("List", "filter");
    private static final ValueName SET_FILTER = ValueName.Stdlib.operation("Set", "filter");
    private static final ValueName LIST_MAP = ValueName.Stdlib.operation("List", "map");

    private static final String SHIPPED_SET_FILTER =
            "Set.fold((acc, x) -> if keep(x) then Set.insert(x, acc) else acc, Set.empty, s)";

    /** Control: the library as shipped keeps where it is said to, a list and a set alike. */
    @Test
    void aListAndASetAreEachProvedToKeepWhereTheClosureHolds() {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();

        assertNotNull(facts.keepsWhereItHolds(LIST_FILTER));
        assertNotNull(facts.keepsWhereItHolds(SET_FILTER));
        assertNull(facts.keepsWhereItHolds(LIST_MAP), "a map keeps no element of its list");
        assertEquals(List.of(), unproved(facts), "nothing stated of it is left open");
    }

    /** A set's step keeping the element where the closure fails is not a filter. */
    @Test
    void aSetStepKeepingTheElementWhereTheClosureFailsIsNoFilter() {
        BoundOperationFacts facts = proved(
                "Set.fold((acc, x) -> if keep(x) then acc else Set.insert(x, acc), Set.empty, s)");

        assertNull(facts.keepsWhereItHolds(SET_FILTER));
        assertEquals(List.of(SET_FILTER), unproved(facts), "stated, and left unproved");
    }

    /** Putting the element in on both ways is keeping it whatever the closure answers. */
    @Test
    void aSetStepKeepingTheElementEitherWayIsNoFilter() {
        assertNull(proved("Set.fold((acc, x) -> if keep(x) then Set.insert(x, acc) "
                + "else Set.insert(x, acc), Set.empty, s)").keepsWhereItHolds(SET_FILTER));
    }

    /** A walk started from the set itself keeps every element, whether or not the closure holds. */
    @Test
    void aSetWalkNotStartedFromNothingIsNoFilter() {
        assertNull(proved("Set.fold((acc, x) -> if keep(x) then Set.insert(x, acc) else acc, "
                + "s, s)").keepsWhereItHolds(SET_FILTER));
    }

    /** Said of an operation that hands no closure the elements it keeps, it is refused. */
    @Test
    void anOperationTakingNoClosureKeepsNothingWhereItHolds() {
        IllegalStateException e = assertThrows(IllegalStateException.class,
                () -> OperationFactBinder.bindAll(DefaultStdlib.get(), declarations(
                        ValueName.Stdlib.operation("List", "length"),
                        new OperationFact.KeepsTheElementsWhereItHolds(
                                new ArgumentRef.TheContainer()))));
        assertTrue(e.getMessage().contains("List.length"), e.getMessage());
    }

    /** The operations it was stated of and not proved. */
    private static List<ValueName> unproved(BoundOperationFacts facts) {
        return facts.notProvedOfTheirBodies().stream()
                .filter(each -> each instanceof BoundOperationFact.KeepsTheElementsWhereItHolds)
                .map(each -> each.operation().operation())
                .toList();
    }

    private static List<OperationFacts.Declared> declarations(ValueName operation,
                                                              OperationFact with) {
        List<OperationFacts.Declared> declared = new ArrayList<>(OperationFacts.declarations());
        declared.add(new OperationFacts.Declared(operation, with));
        return declared;
    }

    /** The library with {@code Set.filter}'s body written as {@code body}, what is kept proved. */
    private static BoundOperationFacts proved(String body) {
        Stdlib stdlib = StdlibLoader.load(text -> text.contains(SHIPPED_SET_FILTER)
                ? text.replace(SHIPPED_SET_FILTER, body) : text);
        return OperationFactBinder.bindAll(stdlib, OperationFacts.declarations().stream()
                .filter(each -> each.fact() instanceof OperationFact.KeepsTheElementsWhereItHolds)
                .toList());
    }
}
