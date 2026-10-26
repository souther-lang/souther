package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.DeclaredSig;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A record whose fields a search holds to ends is composed as every record is: field by field,
 * each against the record's rules with the ones before it settled into them.
 *
 * <p>Each field's ends are what the way leaves it taken alone, and a rule relating two fields is
 * something the ends of neither say. Chosen inside its own ends, each field would be written at
 * its least, and the pair would be one the record's rules refuse.
 */
class AnElementHeldToABoundIsChosenAgainstItsRecordsRulesTest {

    private static final String RELATED = """
            module example.related

            data Span = { lo: Int, hi: Int }
                invariant total = lo + hi == 10

            data Ok

            behavior take : (s: Span) -> Ok

            let take (s) = Ok
            """;

    @Test
    void aFieldTheRulesRelateIsChosenWithTheOneBeforeItSettled() {
        Compilation compilation = compiled();
        Type span = spanOf(compilation);

        Proposals made = Partitions.composedHeldTo((TypeSymbol.AtModule) ((Type.Ref) span).name(),
                (TypeSymbol.AtModule) ((Type.Ref) span).name(), readingOf(compilation),
                heldAtLeast(3, "lo", "hi"));

        assertEquals(List.of("Span { lo = 3, hi = 7 }"),
                made.values().stream().map(FixtureTemplate::text).toList(),
                "the second is chosen where the first leaves the sum, inside its own ends");
    }

    @Test
    void aFieldHeldToNothingIsChosenAsItIsWithoutTheEnds() {
        Compilation compilation = compiled();
        Type span = spanOf(compilation);
        TypeSymbol.AtModule record = (TypeSymbol.AtModule) ((Type.Ref) span).name();

        Proposals made = Partitions.composedHeldTo(record, record, readingOf(compilation),
                Map.of());

        assertTrue(!made.isEmpty(), "a record is composed with no field held");
        assertEquals(Partitions.composed(record, record, readingOf(compilation), java.util.Set.of(),
                                Map.of(), Partitions.RulesAround.NONE)
                        .values().stream().map(FixtureTemplate::text).toList(),
                made.values().stream().map(FixtureTemplate::text).toList(),
                "and it is the record composed without the ends");
    }

    @Test
    void endsNoValueIsInsideComposeNoRecord() {
        Compilation compilation = compiled();
        Type span = spanOf(compilation);
        TypeSymbol.AtModule record = (TypeSymbol.AtModule) ((Type.Ref) span).name();
        Map<String, NumericDomain.Bounds> held = new LinkedHashMap<>();
        held.put("lo", new NumericDomain.Bounds(Endpoint.inclusive(Count.of(8)), null));
        held.put("hi", new NumericDomain.Bounds(Endpoint.inclusive(Count.of(8)), null));

        Proposals made = Partitions.composedHeldTo(record, record, readingOf(compilation), held);

        assertTrue(made.isEmpty(), () -> "the sum cannot be ten from two of at least eight: "
                + made.values());
    }

    private static Map<String, NumericDomain.Bounds> heldAtLeast(long least, String... fields) {
        Map<String, NumericDomain.Bounds> held = new LinkedHashMap<>();
        for (String each : fields) {
            held.put(each, new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)),
                    Endpoint.inclusive(Count.of(10 - least))));
        }
        return held;
    }

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(RELATED, "Main");
        compilation.answerEverything();
        return compilation;
    }

    private static RuleReadingContext readingOf(Compilation compilation) {
        RuleReadingSource rules = RuleReadings.of(compilation, compilation.modules().get(0));
        return RuleReadingContext.of(rules, ReadAs.THE_COMPILATION_DOES,
                compilation.db().readings(), TestDay.TODAY);
    }

    private static Type spanOf(Compilation compilation) {
        Map<String, DeclaredSig> sigs = compilation.db()
                .ask(new Bodies.DeclaredSignatures(compilation.modules().get(0))).value();
        assertNotNull(sigs, "the model did not compile");
        return sigs.get("take").inputs().get(0).type();
    }
}
