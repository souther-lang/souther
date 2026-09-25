package souther.program.api;

import souther.compiler.abort.AbortKind;
import souther.compiler.core.Core;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an output applies a behavior to when it runs a row: the definition computing each input,
 * which is the operand as written, elaborated at the parameter it is handed to.
 *
 * <p>The values a row states are observations, and an observation does not say how the value stands
 * where it is handed over. A case written where its sum is taken stands as the sum, and a value given
 * to an optional field is the optional; an output rebuilding a value out of the observation would
 * decide both again, outside the checker. What crosses instead is the definition the module already
 * holds for the operand, whose body the checker elaborated and whose sites the program answers for.
 */
class ARowsInputIsTheDefinitionComputingItTest {

    private static final String MODULE = """
            module orders

            data Individual = { name: String }
            data Corporation = { company: String }
            data Orderer = Individual | Corporation

            data Quantity = Int
                invariant value > 0

            data Slot = { held: Orderer? }

            behavior named : (orderer: Orderer) -> String
            let named (orderer) = match orderer with
                | Individual as i -> i.name
                | Corporation as c -> c.company

            behavior slotted : (slot: Slot) -> Int
            let slotted (slot) = match slot.held with
                | Some held -> 1
                | None -> 0

            behavior doubled : (q: Quantity) -> Int
            let doubled (q) = q.value * 2

            behavior lookUp : (q: Quantity) -> Int

            behavior counted : (q: Quantity) -> Int
                depends on lookUp
            let counted (q, lookUp) = lookUp(q) + 1

            example named
                | "an individual" : (Individual { name = "ada" }) -> "ada"

            example slotted
                | "one held" : (Slot { held = Corporation { company = "acme" } }) -> 1

            example doubled
                | "two" : (Quantity(2)) -> 4

            fake lookUp
                | (Quantity(2)) -> 10

            example counted
                | "looked up" : (Quantity(2)) -> 11

            example lookUp
                | "owed" : (Quantity(3)) -> <?>
            """;

    private static TypeSymbol.AtModule declared(String name) {
        return TypeSymbols.declared(new TypeKey("orders", name));
    }

    private static CheckedRow firstRow(CheckedProgram program, String behavior) {
        CheckedBehavior of = program.module("orders")
                .behavior(new ValueName.Behavior("orders", behavior));
        return of.rows().getFirst();
    }

    /**
     * A case written where its sum is taken stands as the sum: the definition's body is the case's
     * construction, widened to the parameter's type.
     */
    @Test
    void aCaseWrittenWhereItsSumIsTakenStandsAsTheSum() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedRow.SelfContained row = assertInstanceOf(CheckedRow.SelfContained.class,
                firstRow(program, "named").statement());

        Core.Widen standing = assertInstanceOf(Core.Widen.class,
                row.inputs().getFirst().body());
        assertEquals(Type.ref(declared("Orderer")), standing.type());
        Core.Construct built = assertInstanceOf(Core.Construct.class, standing.value());
        assertEquals(declared("Individual"), built.typeName());
    }

    /** A value given to an optional field is the optional, holding the case standing as the sum. */
    @Test
    void aValueGivenToAnOptionalFieldIsTheOptional() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedRow.SelfContained row = assertInstanceOf(CheckedRow.SelfContained.class,
                firstRow(program, "slotted").statement());

        Core.Construct slot = assertInstanceOf(Core.Construct.class, row.inputs().getFirst().body());
        Core.OptionSome held = assertInstanceOf(Core.OptionSome.class,
                slot.values().getFirst().value());
        Core.Widen standing = assertInstanceOf(Core.Widen.class, held.value());
        assertEquals(Type.ref(declared("Orderer")), standing.type());
    }

    /**
     * The definition is the one the module holds, so what its body can end with is what the
     * program answers for it: a construction of a type that states an invariant can end without a
     * value.
     */
    @Test
    void theDefinitionIsTheModulesAndItsSitesAreAnsweredFor() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("orders");
        CheckedRow.SelfContained row = assertInstanceOf(CheckedRow.SelfContained.class,
                firstRow(program, "doubled").statement());
        CheckedHelper computing = row.inputs().getFirst();

        assertTrue(module.helpers().stream().anyMatch(it -> it == computing),
                () -> computing + " is not among " + module.helpers());
        Core.Construct built = assertInstanceOf(Core.Construct.class, computing.body());
        assertTrue(program.abortsAt(built).contains(AbortKind.INVARIANT_NOT_HELD),
                () -> "what " + built + " can end with is " + program.abortsAt(built));
    }

    /** Every arm that hands over values says what computes them, one for each. */
    @Test
    void everyArmHandingOverValuesSaysWhatComputesThem() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        CheckedRow.WithStandIns stood = assertInstanceOf(CheckedRow.WithStandIns.class,
                firstRow(program, "counted").statement());
        assertEquals(stood.states().inputs().size(), stood.inputs().size());
        assertInstanceOf(Core.Construct.class, stood.inputs().getFirst().body());

        CheckedRow.AnswerOwed owed = assertInstanceOf(CheckedRow.AnswerOwed.class,
                firstRow(program, "lookUp").statement());
        assertEquals(owed.states().inputs().size(), owed.inputs().size());
        assertInstanceOf(Core.Construct.class, owed.inputs().getFirst().body());
    }

    /** Two rows writing the same value are two operands, and each is computed by its own. */
    @Test
    void eachOperandIsComputedByItsOwnDefinition() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedHelper doubled = assertInstanceOf(CheckedRow.SelfContained.class,
                firstRow(program, "doubled").statement()).inputs().getFirst();
        CheckedHelper counted = assertInstanceOf(CheckedRow.WithStandIns.class,
                firstRow(program, "counted").statement()).inputs().getFirst();

        assertTrue(doubled != counted, "two operands share " + doubled);
        assertSame(doubled, assertInstanceOf(CheckedRow.SelfContained.class,
                firstRow(program, "doubled").statement()).inputs().getFirst());
    }
}
