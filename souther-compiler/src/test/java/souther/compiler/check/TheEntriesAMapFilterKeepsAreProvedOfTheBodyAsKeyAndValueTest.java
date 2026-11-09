package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.proof.Library;
import souther.compiler.proof.LibraryProver;
import souther.compiler.proof.WhereTheElementsCameFrom;
import souther.compiler.semantics.ArgumentRef;
import souther.compiler.semantics.OperationFact;
import souther.compiler.semantics.OperationFacts;
import souther.compiler.stdlib.Stdlib;
import souther.compiler.types.ValueName;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Proxy;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    /** A step filing another entry's value under the key keeps the right keys with the wrong
     *  values, and is the same number of entries of values the source holds. */
    @Test
    void aStepFilingAnotherEntrysValueUnderTheKeyIsNoFilter() {
        BoundOperationFacts facts = proved("Map.fold((acc, k, v) -> if keep(k, v) then "
                + "Map.fold((acc2, k2, v2) -> Map.insert(k, v2, acc2), acc, m) else acc, "
                + "Map.empty, m)");

        assertNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertEquals(List.of(FILTER_ENTRIES), unproved(facts), "stated, and left unproved");
    }

    /** A step filing the value under another entry's key keeps the right values under the wrong
     *  keys. */
    @Test
    void aStepFilingTheValueUnderAnotherEntrysKeyIsNoFilter() {
        BoundOperationFacts facts = proved("Map.fold((acc, k, v) -> if keep(k, v) then "
                + "Map.fold((acc2, k2, v2) -> Map.insert(k2, v, acc2), acc, m) else acc, "
                + "Map.empty, m)");

        assertNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertEquals(List.of(FILTER_ENTRIES), unproved(facts), "stated, and left unproved");
    }

    /** A step putting the entry into nothing and not into what was carried drops every entry kept
     *  before it. */
    @Test
    void aStepThatDropsWhatWasKeptBeforeIsNoFilter() {
        BoundOperationFacts facts = proved("Map.fold((acc, k, v) -> if keep(k, v) then "
                + "Map.insert(k, v, Map.empty) else acc, Map.empty, m)");

        assertNull(facts.keepsEntriesWhereItHolds(FILTER_ENTRIES));
        assertEquals(List.of(FILTER_ENTRIES), unproved(facts), "stated, and left unproved");
    }

    /**
     * What is refused of an entry put is what the put files and under which key, and the shipped
     * body is the one read: the library is handed over saying of {@code Map.insert} what it does
     * not do — the value under the key of the value, or the key filed with itself — and the same
     * body is no longer one that keeps the entries. A body written to put wrongly stops being read
     * before its put is reached, so only a library that says it can hold the check to the put.
     */
    @Test
    void aLibrarySayingAPutFilesTheValueUnderTheValueKeepsNoEntry() {
        assertTrue(keptBy(libraryPuttingAs(Function.identity()))
                instanceof LibraryProver.Outcome.Proved, "control: as the library says it");

        assertFalse(keptBy(libraryPuttingAs(put -> new Library.Put(put.value(), put.into(),
                Optional.of(put.value())))) instanceof LibraryProver.Outcome.Proved);
    }

    @Test
    void aLibrarySayingAPutFilesTheKeyAsTheValueKeepsNoEntry() {
        assertFalse(keptBy(libraryPuttingAs(put -> new Library.Put(put.under().orElseThrow(),
                put.into(), put.under()))) instanceof LibraryProver.Outcome.Proved);
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

    /** What is proved of {@code Map.filterEntries}'s shipped body against {@code library}. */
    private static LibraryProver.Outcome keptBy(Library library) {
        BoundOperationFacts facts = DefaultBoundOperationFacts.get();
        BoundOperationFacts.Kept kept = facts.keepsEntriesWhereItHolds(FILTER_ENTRIES);
        return new WhereTheElementsCameFrom(library,
                ProvingTheLibrary.readThrough(DefaultStdlib.get(), facts))
                .keepsEntriesWhereItHolds((ValueName.Stdlib.Operation) FILTER_ENTRIES,
                        kept.source().position(), kept.closure().position());
    }

    /** The shipped library, but saying {@code lie} of what {@code Map.insert} puts. */
    private static Library libraryPuttingAs(Function<Library.Put, Library.Put> lie) {
        Library real = DefaultBoundOperationFacts.library();
        return (Library) Proxy.newProxyInstance(Library.class.getClassLoader(),
                new Class<?>[] {Library.class}, (proxy, method, args) -> {
                    try {
                        Object answer = method.invoke(real, args);
                        return method.getName().equals("puts") && MAP_INSERT.equals(args[0])
                                ? lie.apply((Library.Put) answer) : answer;
                    } catch (InvocationTargetException failed) {
                        throw failed.getCause();
                    }
                });
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
