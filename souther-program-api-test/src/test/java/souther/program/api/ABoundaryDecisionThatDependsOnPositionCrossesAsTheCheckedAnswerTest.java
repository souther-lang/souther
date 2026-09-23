package souther.program.api;

import souther.compiler.program.CheckedAlternativesForm;
import souther.compiler.program.CheckedBoundaryOutput;
import souther.compiler.program.CheckedCodecShape;
import souther.compiler.program.CheckedData;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedSignature;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two positions that hold the same {@link souther.compiler.types.Type} cross differently, and what
 * a checked program hands over is the answer for the position asked about — never the type alone:
 * representation is a function of a value and the position it stands at, not of the value's type by
 * itself.
 *
 * <p>Each case here is one a reader could get right by accident if it only ever saw one program: the
 * value of this test is that the same checked program answers both sides of every pair at once, so
 * a backend that read only the {@link souther.compiler.types.Type} — omission or {@code null},
 * enumeration or discriminated — would be guessing rather than reading.
 */
class ABoundaryDecisionThatDependsOnPositionCrossesAsTheCheckedAnswerTest {

    private static final String MODULE = """
            module demo

            data WithOptField = { note: String? }
            data WithOptElem  = { notes: List<Option<String>> }

            data Standard
            data Extended
            data Agreement = Standard | Extended

            data Failure = { reason: String }
            data Outcome = Standard | Failure

            data Amount = Int
            data Payment = Amount | Failure

            behavior allUnits : (n: Int) -> Standard | Extended
            let allUnits (n) = {
                guard n /= 0 else Standard
                Extended
            }

            behavior mixed : (n: Int) -> Int | Standard
            let mixed (n) = {
                guard n /= 0 else Standard
                n
            }

            behavior nested : (n: Int) -> Agreement | Failure
            let nested (n) = {
                guard n /= 0 else Standard
                Failure { reason = "boom" }
            }
            """;

    private static CheckedModule demo() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("demo");
        assertNotNull(module, "the compile checked this module");
        return module;
    }

    private static CheckedData declared(CheckedModule module, String name) {
        for (CheckedData each : module.data()) {
            if (each.name().name().equals(name)) {
                return each;
            }
        }
        throw new AssertionError(name + " is not among " + module.data());
    }

    private static CheckedSignature signatureOf(CheckedModule module, String behavior) {
        return module.behaviors().stream()
                .filter(each -> each.name().name().equals(behavior))
                .findFirst().orElseThrow(() -> new AssertionError(behavior + " is not declared"))
                .signature();
    }

    /** {@code Option<T>} standing at a field crosses as the field's own shape — an absent value
     *  omits the key (spec {@code [#absence-is-written-as-null]} is the other position's answer). */
    @Test
    void anOptionalFieldsCodecShapeIsTheTopOfWhatTheFieldCarries() {
        CheckedData.WithFields withField =
                assertInstanceOf(CheckedData.WithFields.class, declared(demo(), "WithOptField"));

        CheckedCodecShape note = withField.codecShapes().get(0);

        assertInstanceOf(CheckedCodecShape.OptionOf.class, note,
                "the field's own shape carries the absence, since a field omits its key");
    }

    /** {@code Option<T>} standing at a list element crosses nested a level down — the field's own
     *  shape is the list, and the absence is inside it, which is what says an absent element writes
     *  {@code null} rather than omits anything (there being no key to omit). */
    @Test
    void anOptionalListElementsCodecShapeIsNestedUnderTheList() {
        CheckedData.WithFields withElem =
                assertInstanceOf(CheckedData.WithFields.class, declared(demo(), "WithOptElem"));

        CheckedCodecShape notes = withElem.codecShapes().get(0);

        CheckedCodecShape.ListOf list = assertInstanceOf(CheckedCodecShape.ListOf.class, notes,
                "the field's own shape is the list, not the option standing inside it");
        assertInstanceOf(CheckedCodecShape.OptionOf.class, list.element(),
                "the absence is a level down, where an element has no key to omit");
    }

    /** A sum whose every alternative is a unit travels as a bare tag. */
    @Test
    void allUnitAlternativesTravelAsAnEnumeration() {
        CheckedData.Sum agreement = assertInstanceOf(CheckedData.Sum.class, declared(demo(), "Agreement"));

        assertInstanceOf(CheckedAlternativesForm.Enumeration.class, agreement.representation());
    }

    /** A sum with one alternative that carries something of its own travels discriminated, the unit
     *  case included — the form is a property of the whole set and not of any one case in it. */
    @Test
    void anAlternativeThatCarriesSomethingMakesTheWholeSetDiscriminated() {
        CheckedData.Sum outcome = assertInstanceOf(CheckedData.Sum.class, declared(demo(), "Outcome"));

        CheckedAlternativesForm.Discriminated discriminated =
                assertInstanceOf(CheckedAlternativesForm.Discriminated.class, outcome.representation());
        assertEquals("type", discriminated.tagKey());
        assertEquals("value", discriminated.contentsKey());
    }

    /** The same rule, asked at a behavior's answer instead of a named sum's declaration — both
     *  positions are one question (spec §sum-discrimination) and neither is asked twice. */
    @Test
    void aBehaviorsAnswerUnionIsSettledTheSameWayANamedSumIs() {
        CheckedModule module = demo();

        CheckedBoundaryOutput.Cases allUnits =
                assertInstanceOf(CheckedBoundaryOutput.Cases.class,
                        signatureOf(module, "allUnits").output());
        assertInstanceOf(CheckedAlternativesForm.Enumeration.class, allUnits.representation());

        CheckedBoundaryOutput.Cases mixed =
                assertInstanceOf(CheckedBoundaryOutput.Cases.class,
                        signatureOf(module, "mixed").output());
        assertInstanceOf(CheckedAlternativesForm.Discriminated.class, mixed.representation());
    }

    /**
     * A behavior's answer union may name a sum as one of its members, and what travels at the
     * boundary is the sum's own leaves, not the sum's name: {@code Agreement | Failure} answers
     * with {@code Standard}, {@code Extended} and {@code Failure} on the wire, the same descent a
     * named sum's own cases already make. The union's {@link souther.compiler.types.Type} is the
     * other question — its members are {@code Agreement} and {@code Failure} exactly as written —
     * and a reader wanting the wire form does not reconstruct it from that type, because the type
     * does not hold it.
     */
    @Test
    void aBehaviorsAnswerUnionNamingASumCrossesAtTheSumsLeavesNotItsName() {
        CheckedBoundaryOutput.Cases nested = assertInstanceOf(CheckedBoundaryOutput.Cases.class,
                signatureOf(demo(), "nested").output());

        assertEquals(List.of("Standard", "Extended", "Failure"),
                nested.cases().stream().map(TypeSymbol::name).toList(),
                "the wire cases descend into Agreement rather than naming it");
        assertEquals(Set.of("Agreement", "Failure"),
                nested.type().members().stream().map(TypeSymbol::name).collect(Collectors.toSet()),
                "the semantic type is the union exactly as written, unflattened");
        assertInstanceOf(CheckedAlternativesForm.Discriminated.class, nested.representation(),
                "Failure carries something, so the whole set is discriminated");
    }

    /**
     * One declaration, two positions: {@code Amount} answers for itself as the newtype it is — a
     * bare {@code Int} — and {@code Payment} answers for the sum it stands in, discriminated because
     * {@code Failure} carries something. Neither reading tells a backend what the other would; a
     * reader combining both never asks whether {@code Amount} is "enumeration-eligible" — a newtype
     * is not a unit atom, so it never could be, and nothing here says otherwise by omission.
     */
    @Test
    void aCasesOwnFormAndTheSumsFormAreTwoAnswersAboutTwoPositions() {
        CheckedModule module = demo();

        CheckedData.Newtype amount = assertInstanceOf(CheckedData.Newtype.class, declared(module, "Amount"));
        CheckedData.Sum payment = assertInstanceOf(CheckedData.Sum.class, declared(module, "Payment"));

        assertEquals(Type.INT, amount.wrapped(),
                "Amount answers for itself: a bare Int");
        assertInstanceOf(CheckedAlternativesForm.Discriminated.class, payment.representation(),
                "Payment answers for the sum: Failure carries something, so the set is discriminated");
        assertEquals(List.of("Amount", "Failure"),
                payment.cases().stream().map(TypeSymbol::name).toList());
    }
}
