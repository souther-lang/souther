package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.carrier.Membership;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.Position;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A rule asking a map for an entry under the key standing in another field is a rule of the two
 * fields together, and is read at both.
 *
 * <p>{@code Map.containsKey(base, rates)}, and the lookup {@code Map.get(base, rates)} followed to
 * a comparison of what it found with a written number, absent counting as false. Read as a form
 * nothing takes apart, the rule left a question standing at both fields.
 */
class AMapAskedForAnEntryUnderAKeyBesideItIsReadTest {

    private static final String BEHAVIOR = """

            behavior probe : (n: N) -> Int
            let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
            """;

    private static String table(String fields, String invariant, String helper) {
        return """
                module demo

                data CurrencyCode = String
                    invariant String.matches("[A-Z]{3}", value)
                data ConversionRate = Decimal
                    invariant value > 0.0m

                data N = { %s }
                    invariant baseIsUnity = %s

                %s
                """.formatted(fields, invariant, helper) + BEHAVIOR;
    }

    private static final String BASE_THEN_RATES =
            "base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>";

    private static String lookup(String comparison) {
        return """
                let baseAtRate (base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>): Bool =
                    Map.get(base, rates)
                        |> Option.map(r -> %s)
                        |> Option.withDefault(false)
                """.formatted(comparison);
    }

    @Test
    void aMembershipTestIsReadAtTheKeyAndTheMap() {
        assertEquals(Map.of("n.base", List.of(), "n.rates", List.of()),
                unansweredAtTheFields(table(BASE_THEN_RATES, "Map.containsKey(base, rates)", "")));
    }

    @Test
    void aLookupComparedWithAWrittenNumberIsReadAtTheKeyAndTheMap() {
        String model = table(BASE_THEN_RATES, "baseAtRate(base, rates)",
                lookup("Decimal.compare(r.value, 1.0m) == 0"));

        assertEquals(Map.of("n.base", List.of(), "n.rates", List.of()),
                unansweredAtTheFields(model));
    }

    @Test
    void aLookupThatOnlyBoundsTheValueFoundStaysUnanswered() {
        String model = table(BASE_THEN_RATES, "baseAtRate(base, rates)",
                lookup("Decimal.compare(r.value, 1.0m) >= 0"));

        Map<String, List<String>> left = unansweredAtTheFields(model);

        assertFalse(left.get("n.base").isEmpty(),
                "a builder told the entry exists would build maps the rule refuses");
        assertFalse(left.get("n.rates").isEmpty());
    }

    private static final String TWO_ENTRIES = """
            module demo

            data N = { x: String, y: String, rates: Map<String, Int> }
                invariant atX = atKey(x, rates, 1)
                invariant atY = atKey(y, rates, 2)

            let atKey (k: String, m: Map<String, Int>, n: Int): Bool =
                Map.get(k, m)
                    |> Option.map(r -> r == n)
                    |> Option.withDefault(false)
            """;

    /**
     * Two entries asked of one map, each under a key of its own and a number of its own, are keys
     * together: they may come to one value, or be more than their type has, and a reading of each
     * place alone does not ask that. The map is still built holding both; no key is called free.
     */
    @Test
    void twoEntriesAskedOfOneMapAreNotCalledFreeAtTheKeys() {
        Map<String, List<String>> left = unansweredAtTheFields(TWO_ENTRIES + BEHAVIOR);

        assertFalse(left.get("n.x").isEmpty());
        assertFalse(left.get("n.y").isEmpty());
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A rule of the record that was listed and nothing was made of may ask the same map the
     * opposite: {@code key} held in the map and the key {@code 0} not, which no map beside a key of
     * nought satisfies. Listing a rule is not reading it, and the entry asked for is not built
     * beside it.
     */
    @Test
    void aRuleOfTheRecordNothingWasMadeOfLeavesTheMapUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, rates: Map<Int, Int> }
                    invariant held = Map.containsKey(key, rates)
                    invariant notNought = Bool.not(Map.containsKey(0, rates))

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty(), "a key of nought has no map beside it");
        assertFalse(left.get("n.rates").isEmpty(), "a rule asking the map the opposite is unread");
    }

    /**
     * The same, whatever the other rule is written as: it is the map it reads from that matters and
     * not the shape of what it says of it. Two keys held at once are forbidden, and the record holds
     * the key {@code 1} by the first rules, so the key nought is no key of any map beside it.
     */
    @Test
    void aRuleDenyingTwoKeysTogetherLeavesTheMapAndItsKeyUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, required: Int, rates: Map<Int, Int> }
                    invariant fixed = required == 1
                    invariant heldKey = Map.containsKey(key, rates)
                    invariant heldRequired = Map.containsKey(required, rates)
                    invariant notBoth = Bool.not(
                        Map.containsKey(0, rates) && Map.containsKey(1, rates))

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty(), "a key of nought has no map beside it");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A rule that reads the map only to count what it holds is the count the range of the map
     * already carries, and the builders hold the entry beside it. How many a map holds is how many
     * keys the key's type must have, which this reading does not ask, so the key is not called
     * free beside it.
     */
    @Test
    void aRuleCountingTheMapLeavesTheKeyUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, rates: Map<Int, Int> }
                    invariant held = Map.containsKey(key, rates)
                    invariant some = Map.size(rates) >= 1

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty());
        assertFalse(left.get("n.rates").isEmpty());
    }

    /** One entry asked of a map nothing else asks anything of is the shape a key is called free
     *  for. */
    @Test
    void oneEntryAskedOfAMapNothingElseAsksOfLeavesTheKeyRead() {
        assertEquals(Map.of("n.key", List.of(), "n.rates", List.of()),
                unansweredAtTheFields("""
                        module demo

                        data N = { key: Int, rates: Map<Int, Int> }
                            invariant held = Map.containsKey(key, rates)

                        behavior probe : (n: N) -> Int
                        let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                        """));
    }

    private static final String FIXED_ENTRY = """
            module demo

            data N = { key: Int, required: Int, rates: Map<Int, Int> }
                invariant fixed = required == 0
                invariant held = Map.containsKey(key, rates)
                invariant requiredEntry = Map.containsKey(required, rates)
                invariant small = Map.size(rates) <= 2
                %s

            behavior probe : (n: N) -> Int
            let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
            """;

    /**
     * A rule about how many the map holds is the interval its range carries only when it is one:
     * a count that must be odd, or must not be one, leaves holes in the interval, and the map
     * holding exactly the entry required is the one map the rules allow, so the key is that entry's.
     */
    @Test
    void aCountThatIsNotAnIntervalIsARuleReadingTheMap() {
        for (String rule : List.of(
                "invariant odd = Int.floorMod(Map.size(rates), 2) == 1",
                "invariant notTwo = Bool.not(Map.size(rates) == 2)")) {
            Map<String, List<String>> left = unansweredAtTheFields(FIXED_ENTRY.formatted(rule));

            assertFalse(left.get("n.key").isEmpty(), rule);
            assertFalse(left.get("n.rates").isEmpty(), rule);
        }
    }


    /**
     * That a map can be built holding the entries asked of it is not that it can be for every key
     * the key's own place admits. Two entries asked of a map that holds one are two keys, and the
     * key beside the one required is a key no map holds.
     */
    @Test
    void aKeyIsNotFreeWhereTheMapCannotHoldTheEntriesOfEveryKey() {
        Map<String, List<String>> left = unansweredAtTheFields(FIXED_ENTRY.formatted("""
                invariant one = Map.size(rates) == 1"""));

        assertFalse(left.get("n.key").isEmpty(), "only the key nought has a map of one entry");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * And where another key is fixed by a rule of the record, the key beside it is not free either:
     * one key asked for two numbers is no map.
     */
    @Test
    void aKeyIsNotFreeBesideAnotherKeyTheRecordFixes() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { x: String, y: String, rates: Map<String, Int> }
                    invariant fixedY = y == "a"
                    invariant atX = atKey(x, rates, 1)
                    invariant atY = atKey(y, rates, 2)

                let atKey (k: String, m: Map<String, Int>, n: Int): Bool =
                    Map.get(k, m)
                        |> Option.map(r -> r == n)
                        |> Option.withDefault(false)
                """ + BEHAVIOR);

        assertFalse(left.get("n.x").isEmpty(), "the key a is the other key's");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * Three entries asked of a map under keys of a type with two values are keys no map holds
     * apart. The keys together are a question the reading of each place alone does not ask, so none
     * is called free.
     */
    @Test
    void keysOfATypeWithTooFewValuesAreNotFree() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data Stage = Open | Closed

                data N = { a: Stage, b: Stage, c: Stage, byStage: Map<Stage, Int> }
                    invariant aHasOne = atKey(a, byStage, 1)
                    invariant bHasTwo = atKey(b, byStage, 2)
                    invariant cHasThree = atKey(c, byStage, 3)

                let atKey (k: Stage, m: Map<Stage, Int>, n: Int): Bool =
                    Map.get(k, m)
                        |> Option.map(r -> r == n)
                        |> Option.withDefault(false)
                """ + BEHAVIOR.replace("n.rates", "n.byStage"));

        assertFalse(left.get("n.a").isEmpty());
        assertFalse(left.get("n.byStage").isEmpty());
    }

    /**
     * A number asked of the value that the value's type refuses is an entry that cannot be written,
     * and a key is not free for an entry nothing writes.
     */
    @Test
    void aKeyIsNotFreeForAValueItsTypeRefuses() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data Positive = Int
                    invariant value > 0

                data N = { key: Int, rates: Map<Int, Positive> }
                    invariant held = Map.containsKey(key, rates)
                    invariant isNought = zeroAt(key, rates)

                let zeroAt (k: Int, m: Map<Int, Positive>): Bool =
                    Map.get(k, m)
                        |> Option.map(r -> r.value == 0)
                        |> Option.withDefault(false)
                """ + BEHAVIOR);

        assertFalse(left.get("n.key").isEmpty(), "no map holds a value of nought");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A bound on how many a field holds is the count the range of a container already carries, and
     * is not that of a key: the length of a key is the key's own value, and a key the record
     * allows only the empty string is a key the other is not.
     */
    @Test
    void aLengthOfAnotherKeyIsARuleReadingIt() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { x: String, y: String, rates: Map<String, Int> }
                    invariant fixedY = String.length(y) == 0
                    invariant atX = atKey(x, rates, 1)
                    invariant atY = atKey(y, rates, 2)

                let atKey (k: String, m: Map<String, Int>, n: Int): Bool =
                    Map.get(k, m)
                        |> Option.map(r -> r == n)
                        |> Option.withDefault(false)
                """ + BEHAVIOR);

        assertFalse(left.get("n.x").isEmpty(), "the empty string is the other key's");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A count of a map made from the field is not the count the field's range carries: the
     * map without the key nought has as many entries as the field only where it holds no such
     * entry, so the rule says the key is not nought.
     */
    @Test
    void aCountOfTheMapWithAnEntryRemovedIsARuleReadingTheMap() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, rates: Map<Int, Int> }
                    invariant held = Map.containsKey(key, rates)
                    invariant noZero = Map.size(Map.remove(0, rates)) == Map.size(rates)

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty(), "a key of nought has no map beside it");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A rule of the shape the builders know, asked of a map made from the field, is recognised and
     * not built for: the map it asks the entry of is not a field. That it was recognised does not
     * make it a rule the field is built holding.
     */
    @Test
    void aRuleRecognisedAndNotBuiltForIsStillARuleReadingTheMap() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data N = { key: Int, rates: Map<Int, Int> }
                    invariant held = Map.containsKey(key, rates)
                    invariant one = Map.size(rates) == 1
                    invariant required = Map.containsKey(1, Map.remove(0, rates))

                behavior probe : (n: N) -> Int
                let probe (n) = if Map.size(n.rates) >= 0 then 1 else 2
                """);

        assertFalse(left.get("n.key").isEmpty(), "only the key one is held by such a map");
        assertFalse(left.get("n.rates").isEmpty());
    }

    /**
     * A key that is not a field of the record is a key the builders are never told of, because a
     * record's fields are chosen one at a time and a key is chosen before the map it is a key of.
     * The rule is left standing rather than called read.
     */
    @Test
    void aKeyThatIsNotAFieldOfTheRecordLeavesTheMapUnanswered() {
        Map<String, List<String>> left = unansweredAtTheFields("""
                module demo

                data Inner = { k: String }
                data N = { inner: Inner, rates: Map<String, Int> }
                    invariant has = Map.containsKey(inner.k, rates)
                """ + BEHAVIOR);

        assertFalse(left.get("n.rates").isEmpty(), "nothing builds a map for a key it cannot reach");
    }

    /** What stands unanswered at each field of the input of {@code probe}, by field. */
    private static Map<String, List<String>> unansweredAtTheFields(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        String module = compilation.modules().get(0);
        Map<String, DeclaredSig> sigs =
                compilation.db().ask(new Bodies.DeclaredSignatures(module)).value();
        RuleReadingContext reading = RuleReadingContext.unshared(
                RuleReadings.of(compilation, module), ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);
        Map<String, List<String>> out = new LinkedHashMap<>();
        for (Position each : InputDomain.of(sigs.get("probe"), reading,
                TypeCardinality.Counts.workedOutIn(reading), Membership.none()).positions()) {
            String path = each.path().toString();
            if (path.startsWith("n.") && path.indexOf('.', 2) < 0 && !path.contains("[")) {
                out.put(path, each.unansweredQuestions().stream()
                        .map(question -> question.rule().toString()).toList());
            }
        }
        return out;
    }
}
