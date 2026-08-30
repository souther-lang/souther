package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What {@link Limits} admits, at each bound and one past it.
 *
 * <p>Every number here is a boundary and its two neighbours. A limit tested with a value well
 * inside it and one well outside it passes for an implementation that is off by one everywhere,
 * and off by one is the whole of what there is to get wrong: the walk that produces an observation
 * and the predicate that judges one already read are two readings of these numbers, and they agree
 * only if each says the same thing about the value that stands exactly at the bound.
 *
 * <p>Asked of both halves of a value. What a text stated and what a run answered are counted by one
 * set of numbers, so a value written as an {@link Asserted} and the same value observed have to be
 * admitted or refused together.
 */
class ALimitAdmitsWhatStandsAtItsBoundAndNothingOverItTest {

    private static final TypeSymbol.AtModule A_DATA =
            TypeSymbols.declared(new TypeKey("demo", "Receipt"));

    @Test
    void aCollectionOfAsManyElementsAsAreKeptIsAdmitted() {
        assertTrue(Limits.DEFAULT.admits(sequenceOf(63)), "63 elements");
        assertTrue(Limits.DEFAULT.admits(sequenceOf(64)), "64 elements");
        assertFalse(Limits.DEFAULT.admits(sequenceOf(65)), "65 elements");
    }

    @Test
    void andTheSameCountsAMapsEntries() {
        assertTrue(Limits.DEFAULT.admits(entriesOf(64)), "64 entries");
        assertFalse(Limits.DEFAULT.admits(entriesOf(65)), "65 entries");
    }

    @Test
    void aValueAsDeepAsTheWalkGoesIsAdmitted() {
        assertTrue(Limits.DEFAULT.admits(nested(11)), "deepest at 11");
        assertTrue(Limits.DEFAULT.admits(nested(12)), "deepest at 12");
        assertFalse(Limits.DEFAULT.admits(nested(13)), "deepest at 13");
    }

    @Test
    void aTextOfAsManyCharactersAsAreKeptIsAdmitted() {
        assertTrue(Limits.DEFAULT.admits(text(1023)), "1023 characters");
        assertTrue(Limits.DEFAULT.admits(text(1024)), "1024 characters");
        assertFalse(Limits.DEFAULT.admits(text(1025)), "1025 characters");
    }

    /**
     * The node budget is one for the whole value, and a construction's fields are nodes of it.
     *
     * <p>A data with 1999 fields is 2000 nodes with the data itself, which is the budget exactly.
     * Fields rather than elements, because how many elements one collection keeps is a second limit
     * and a value written to reach the node budget through a collection would reach that one first.
     */
    @Test
    void aValueOfAsManyNodesAsTheBudgetHoldsIsAdmitted() {
        assertTrue(Limits.DEFAULT.admits(fields(1999)), "2000 nodes");
        assertFalse(Limits.DEFAULT.admits(fields(2000)), "2001 nodes");
    }

    /**
     * A stated scalar is the observed value it holds and not a node standing over one.
     *
     * <p>The one place the two walks could come apart by construction: an {@link Asserted.Value}
     * wraps an {@link ObservedValue}, and charging for both would make one value cost twice what
     * the same value costs when it is observed.
     */
    @Test
    void aStatedScalarCostsWhatAnObservedOneCosts() {
        assertTrue(Limits.DEFAULT.admits(statedFields(1999)), "2000 nodes");
        assertFalse(Limits.DEFAULT.admits(statedFields(2000)), "2001 nodes");
    }

    /** Neither case is a value, wherever in the value it stands. */
    @Test
    void nothingHoldingAValueThatCouldNotBeReadIsAdmitted() {
        assertFalse(Limits.DEFAULT.admits(new ObservedValue.Truncated()), "truncated");
        assertFalse(Limits.DEFAULT.admits(new ObservedValue.Unknown("why")), "unreadable");
        assertFalse(Limits.DEFAULT.admits(new ObservedValue.Sequence(
                List.of(new ObservedValue.Integer(1), new ObservedValue.Truncated()))),
                "truncated inside a sequence");
        assertFalse(Limits.DEFAULT.admits(new Asserted.Elements(Asserted.Container.LIST,
                List.of(new Asserted.Value(new ObservedValue.Unknown("why"))))),
                "unreadable inside what was stated");
    }

    /** And a value that is there in full is, so the answers above are not one answer to everything. */
    @Test
    void andAValueThatIsThereInFullIsAdmitted() {
        assertTrue(Limits.DEFAULT.admits(new ObservedValue.Integer(1)));
        assertTrue(Limits.DEFAULT.admits(new Asserted.Value(new ObservedValue.Integer(1))));
    }

    private static ObservedValue sequenceOf(int elements) {
        List<ObservedValue> out = new ArrayList<>();
        for (int i = 0; i < elements; i++) {
            out.add(new ObservedValue.Integer(i));
        }
        return new ObservedValue.Sequence(out);
    }

    private static ObservedValue entriesOf(int entries) {
        List<ObservedValue.Entry> out = new ArrayList<>();
        for (int i = 0; i < entries; i++) {
            out.add(new ObservedValue.Entry(new ObservedValue.Integer(i),
                    new ObservedValue.Integer(i)));
        }
        return new ObservedValue.Mapping(out);
    }

    /** A value whose deepest node stands at {@code depth}, the root being at zero. */
    private static ObservedValue nested(int depth) {
        ObservedValue at = new ObservedValue.Integer(1);
        for (int i = 0; i < depth; i++) {
            Map<String, ObservedValue> fields = ObservedValue.fields();
            fields.put("value", at);
            at = new ObservedValue.Constructed(A_DATA, fields);
        }
        return at;
    }

    private static ObservedValue text(int characters) {
        return new ObservedValue.Text("x".repeat(characters));
    }

    private static ObservedValue fields(int count) {
        Map<String, ObservedValue> fields = ObservedValue.fields();
        for (int i = 0; i < count; i++) {
            fields.put("f" + i, new ObservedValue.Integer(i));
        }
        return new ObservedValue.Constructed(A_DATA, fields);
    }

    private static Asserted statedFields(int count) {
        Map<String, Asserted> fields = new LinkedHashMap<>();
        for (int i = 0; i < count; i++) {
            fields.put("f" + i, new Asserted.Value(new ObservedValue.Integer(i)));
        }
        return new Asserted.Built(A_DATA, fields);
    }
}
