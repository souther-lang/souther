package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule asking whether a key is among a map's keys asks the map for an entry under it, however
 * the membership is written: as the map's own test, or as the test of a list on the list of the
 * map's keys. Which operation asks whether a container holds a value, and which lists a map's keys,
 * is what the library's laws say of them, so the second is the first and not a spelling learnt.
 *
 * <p>{@code Map.containsKey} is the oracle: each spelling asks the map for what it asks, and is
 * accounted for as it is. A list of the map's values holds no key, and is the control.
 */
class AMembershipOfAMapsKeysIsTheEntryTheMapIsHeldToTest {

    private static final String ORACLE = "Map.containsKey(key, table)";

    private record Read(Map<RuleKey, List<EntryHeld.Requirement>> entries, boolean accounted) {}

    private static Read read(String rule) {
        Compilation compilation = Compilation.ofSource("""
                module demo

                data N = { key: String, table: Map<String, String> }
                    invariant %s
                """.formatted(rule), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey("demo", "N"));
        FieldDomains domains = FieldDomains.of(named,
                RuleReadingContext.unshared(rules, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY));
        return new Read(EntryHeld.writtenOn(named, rules), domains.accounting().values().stream()
                .allMatch(each -> each.unaccounted().isEmpty()));
    }

    @Test
    void aMembershipOfTheMapsKeysAsksTheMapForTheEntry() {
        Read oracle = read(ORACLE);
        assertFalse(oracle.entries().isEmpty(), "the oracle asks the map for an entry");
        assertTrue(oracle.accounted(), "and is accounted for");
        for (String rule : List.of("List.contains(key, Map.keys(table))",
                "{\n        let ks = Map.keys(table)\n        List.contains(key, ks)\n    }")) {
            assertEquals(oracle, read(rule), rule);
        }
    }

    @Test
    void aListOfTheMapsValuesHoldsNoKey() {
        assertEquals(Map.of(), read("List.contains(key, Map.values(table))").entries());
    }
}
