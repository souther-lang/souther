package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.CheckSurface;
import souther.compiler.check.Prepared;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Sig;
import souther.compiler.coverage.ConditionOutcomeSite;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.CountWitnesses;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.types.FixtureReferenceOrigin;
import souther.compiler.types.Type;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count of the elements a statement holds of is witnessed by a row: one element it holds of and
 * one it fails of, beside one value of everything else, each input built by the boundary and the
 * behavior answering on it ({@link CountWitnesses}).
 *
 * <p>The values tried are found, and finding one is no claim: a value the model names is tried at
 * its type, a value standing for a type is tried, and an element is made to hold, where a
 * statement says it is the same value as a place outside the container, each value the row holds
 * there. What the boundary refuses is not a witness, and a value refused is not every value
 * refused.
 */
class ACountIsWitnessedByARowTheBoundaryBuildsAndTheBehaviorAnswersTest {

    /** A table whose rule — the base in it at one — reads a key and its value together. */
    private static final String RATES = """
            data CurrencyCode = String
                invariant String.matches("[A-Z]{3}", value)

            data ConversionRate = Decimal
                invariant value > 0.0m

            data RateTable =
                { base: CurrencyCode
                , rates: Map<CurrencyCode, ConversionRate>
                }
                invariant baseIsUnity = baseAtOne(base, rates)

            let baseAtOne (base: CurrencyCode, rates: Map<CurrencyCode, ConversionRate>): Bool =
                Map.get(base, rates)
                    |> Option.map(r -> Decimal.compare(r.value, 1.0m) == 0)
                    |> Option.withDefault(false)

            let yenRates = RateTable { base = CurrencyCode("JPY"), rates = Map.fromList(
                [ (CurrencyCode("JPY"), ConversionRate(1.0m))
                , (CurrencyCode("USD"), ConversionRate(150.0m)) ]) }

            let broken = RateTable { base = CurrencyCode("AAA"), rates = Map.empty }
            """;

    /** A forecast keeping the deals whose currency the table has, held to keeping every one. */
    private static String forecast(String deal, String depends) {
        return """
                module demo

                %s

                %s

                data Ok
                data Lost

                behavior forecast : (deals: List<Deal>, rates: RateTable) -> Ok | Lost
                %s

                let forecast (deals, rates) = {
                    let kept = List.filterMap(d -> Map.get(d.currency, rates.rates), deals)
                    guard List.length(kept) == List.length(deals) else Lost
                    Ok
                }
                """.formatted(RATES, deal, depends);
    }

    private static final String DEAL = "data Deal = { currency: CurrencyCode, amount: Decimal }";

    private static final String ROWS = """

            example forecast
                | "none" : ([], yenRates) -> Ok
                | "kept" : ([ Deal { currency = CurrencyCode("JPY"), amount = 1.0m } ], yenRates)
                    -> Ok
                | "dropped" : ([ Deal { currency = CurrencyCode("AAA"), amount = 1.0m } ],
                    yenRates) -> Lost
                | "mixed" : ([ Deal { currency = CurrencyCode("JPY"), amount = 1.0m }
                            , Deal { currency = CurrencyCode("AAA"), amount = 1.0m } ], yenRates)
                    -> Lost
            """;

    private static final TermPath DEALS = TermPath.of("deals");

    private static final TermPath MAP = TermPath.of("rates").then("rates");

    /** How many deals have a currency some key of the table is. */
    private static final Quantity.HowManyMeet COUNT = new Quantity.HowManyMeet(
            new DecisionSubject.AnInput(DEALS),
            new Proposition.Some(new DecisionSubject.AnInput(MAP),
                    new Proposition.SameValue(new DecisionSubject.AnInput(MAP.key()),
                            new DecisionSubject.AnInput(DEALS.element().then("currency")), true),
                    true));

    private static Compilation compiled(String source) {
        Compilation compilation = Compilation.ofSources(List.of(source), ModulePath.EMPTY);
        compilation.measure(Adequacy.Asked.fullReport());
        assertEquals(List.of(), compilation.errors(), "the model under test compiles");
        assertEquals(List.of("demo"), compilation.modules(), "and is read");
        return compilation;
    }

    private static Optional<CountWitnesses.Witness> witnessIn(Compilation compilation) {
        return compilation.db().ask(askedIn(compilation, COUNT)).value().found();
    }

    /** {@code count}'s witness, at a run going through the comparison the body writes. */
    private static Adequacy.WitnessOfACount askedIn(Compilation compilation,
                                                    Quantity.HowManyMeet count) {
        Set<ConditionOutcomeSite> reaching = new HashSet<>();
        compilation.db().ask(new Bodies.Observable("demo")).value().plan().sites().forEach(site -> {
            if (site instanceof CoverageSites.ComparisonSite compared
                    && compared.body().equals("forecast")) {
                reaching.add(compared.index());
            }
        });
        return new Adequacy.WitnessOfACount("demo", "forecast", count, reaching);
    }

    /** The table the model names is the one tried, and an element is made to hold one of its
     *  keys: the row keeps one deal and drops the other, and the behavior answers on it. */
    @Test
    void aRowKeepingOneElementAndDroppingAnotherBesideOneTableIsFound() {
        Optional<CountWitnesses.Witness> found = witnessIn(compiled(forecast(DEAL, "")));
        assertTrue(found.isPresent(), "a witness is found");
        assertEquals(List.of("[Deal { currency = CurrencyCode(\"USD\"), amount = 0m },"
                        + " Deal { currency = CurrencyCode(\"AAA\"), amount = 0m }]", "yenRates"),
                found.get().inputs().stream().map(FixtureTemplate::text).toList());
    }

    /** A value of the table's type the model names is built where its rule holds and refused
     *  where it does not: which is valid is the boundary's to say. */
    @Test
    void aNamedValueIsBuiltWhereItsRulesHoldAndRefusedWhereTheyDoNot() {
        Compilation compilation = compiled(forecast(DEAL, ""));
        CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface("demo")).value();
        FixturesAtTheBoundary building = Adequacy.constructing(compilation.db(), "demo");
        assertNotNull(building);
        List<String> built = surface.typedFixtureValues().values().stream()
                .flatMap(List::stream)
                .map(named -> named.rendered() + " " + (building.buildAlone(
                        typeOfTheTable(surface), FixtureTemplate.named(named,
                                new FixtureReferenceOrigin(0)))
                        instanceof BoundaryValues.OnItsOwn.Built ? "BUILT" : "REFUSED"))
                .sorted().toList();
        assertEquals(List.of("broken REFUSED", "yenRates BUILT"), built);
    }

    /** Each row written is counted at the elements the statement holds of, every element told. */
    @Test
    void eachRowIsCountedAtTheElementsTheStatementHoldsOf() {
        Compilation compilation = compiled(forecast(DEAL, "") + ROWS);
        Db db = compilation.db();
        Sig sig = db.ask(new Bodies.Signatures("demo")).value().get("forecast");
        FixturesAtTheBoundary building = Adequacy.constructing(db, "demo");
        InputReading read = db.ask(new Adequacy.Inputs("demo")).value().get("forecast")
                .reading(RuleReadings.of(compilation, "demo"));
        Prepared prepared = db.ask(new Shapes.Prepared("demo")).value();
        for (var expected : List.of(List.of("none", "0"), List.of("kept", "1"),
                List.of("dropped", "0"), List.of("mixed", "1"))) {
            Hir.ExampleRow row = prepared.examples().stream().map(Prepared.Example::read)
                    .flatMap(block -> block.rows().stream())
                    .filter(each -> each.identity().shown().equals(expected.get(0)))
                    .findFirst().orElseThrow();
            assertEquals(Optional.of(Integer.valueOf(expected.get(1))),
                    CountWitnesses.metOn(COUNT, "forecast", read, row.inputs().stream()
                                    .map(input -> new FixtureTemplate(expected.get(0), input))
                                    .toList(),
                            (at, fixture) -> building.build(sig.ins().get(at), fixture)
                                    instanceof BoundaryValues.Built.Value(ObservedValue value)
                                    ? Optional.of(value) : Optional.<ObservedValue>empty()),
                    expected.get(0));
        }
    }

    /** An element made to hold a key its own rule refuses is no witness, and the search goes on
     *  to the next key; where its rule refuses every key, nothing is found. */
    @Test
    void anElementItsOwnRuleRefusesIsPassedOverAndNotTakenForEveryOne() {
        String notDollars = DEAL + "\n    invariant currency.value /= \"USD\"";
        Optional<CountWitnesses.Witness> found = witnessIn(compiled(forecast(notDollars, "")));
        assertTrue(found.isPresent(), "the other key is tried");
        assertEquals("Deal { currency = CurrencyCode(\"JPY\"), amount = 0m }",
                found.get().kept().text());
        String neither = DEAL + "\n    invariant currency.value /= \"USD\""
                + " && currency.value /= \"JPY\"";
        assertEquals(Optional.empty(), witnessIn(compiled(forecast(neither, ""))));
    }

    /** A behavior that depends on another runs only with it stood in for, which nothing here
     *  answers: nothing is found, which says nothing of whether a witness exists. */
    @Test
    void aBehaviorThatDependsOnAnotherIsWitnessedByNothing() {
        String depending = """
                    depends on today

                behavior today : () -> Int
                """;
        assertEquals(Optional.empty(), witnessIn(compiled(forecast(DEAL, depending))));
    }

    /** Asked twice it is answered once, and another count is asked apart. */
    @Test
    void oneCountIsWitnessedOnceAndAnotherApart() {
        Compilation compilation = compiled(forecast(DEAL, ""));
        Optional<CountWitnesses.Witness> first = witnessIn(compilation);
        assertSame(first, witnessIn(compilation));
        Quantity.HowManyMeet other = new Quantity.HowManyMeet(new DecisionSubject.AnInput(DEALS),
                new Proposition.Some(new DecisionSubject.AnInput(MAP),
                        new Proposition.SameValue(new DecisionSubject.AnInput(MAP.key()),
                                new DecisionSubject.AnInput(DEALS.element().then("currency")),
                                true),
                        false));
        Adequacy.WitnessOfACount asked = askedIn(compilation, other);
        compilation.db().ask(asked);
        assertTrue(compilation.db().isComputed(asked), "the other count is a question of its own");
    }

    /** What a witness is found from is below any division: nothing it reads, on down, divides
     *  the behavior or walks the way to a comparison. */
    @Test
    void aWitnessIsFoundBelowAnyDivision() {
        Compilation compilation = compiled(forecast(DEAL, ""));
        Adequacy.WitnessOfACount asked = askedIn(compilation, COUNT);
        compilation.db().ask(asked);
        Set<Key<?>> reached = new HashSet<>();
        Set<String> read = new HashSet<>();
        Deque<Key<?>> left = new ArrayDeque<>(List.of(asked));
        while (!left.isEmpty()) {
            for (Key<?> each : compilation.db().dependenciesOf(left.pop())) {
                if (reached.add(each)) {
                    read.add(each.getClass().getName());
                    left.push(each);
                }
            }
        }
        for (String division : List.of(Adequacy.Divided.class.getName(),
                Adequacy.Dividing.class.getName(), Adequacy.Arrived.class.getName(),
                Adequacy.Coverage.class.getName())) {
            assertTrue(!read.contains(division), () -> division + " in " + read);
        }
    }

    private static Type typeOfTheTable(CheckSurface surface) {
        return surface.typedFixtureValues().keySet().stream()
                .filter(type -> type.toString().contains("RateTable")).findFirst().orElseThrow();
    }
}
