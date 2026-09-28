package souther.program.api;

import souther.compiler.abort.AbortKind;
import souther.compiler.core.Core;
import souther.compiler.observe.RowIdentity;
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
import static org.junit.jupiter.api.Assertions.assertNotSame;
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

            behavior everyone : (orderers: List<Orderer>) -> Int
            let everyone (orderers) = List.length(orderers)

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

            example everyone
                | "both kinds" : ([Individual { name = "ada" }, Corporation { company = "acme" }]) -> 2

            example doubled
                | "two" : (Quantity(2)) -> 4

            fake lookUp
                | (Quantity(2)) -> 10

            example counted
                | "looked up" : (Quantity(2)) -> 11

            example lookUp
                | "owed" : (Quantity(3)) -> <?>
            """;

    /** Rows of the same module written in a file of their own, after the module's. */
    private static final String ATTACHED = """
            examples for orders

            example named
                | "a corporation" : (Corporation { company = "acme" }) -> "acme"
            """;

    private static TypeSymbol.AtModule declared(String name) {
        return TypeSymbols.declared(new TypeKey("orders", name));
    }

    private static CheckedRow row(CheckedProgram program, String behavior, String named) {
        CheckedBehavior of = program.module("orders")
                .behavior(new ValueName.Behavior("orders", behavior));
        return of.rows().stream()
                .filter(it -> it.identity().equals(new RowIdentity.Named(named)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + named + "` among " + of.rows()));
    }

    private static CheckedHelper computingOnlyInput(CheckedRow row) {
        List<CheckedHelper> definitions = switch (row.statement()) {
            case CheckedRow.SelfContained it -> it.inputDefinitions();
            case CheckedRow.WithStandIns it -> it.inputDefinitions();
            case CheckedRow.AnswerOwed it -> it.inputDefinitions();
            case CheckedRow.NotReproducible it ->
                    throw new AssertionError("the row states no values: " + it.why());
        };
        assertEquals(1, definitions.size(), () -> "what computes " + row + " is " + definitions);
        return definitions.getFirst();
    }

    /** The case a definition's body builds, standing as {@code at}. */
    private static TypeSymbol.AtModule caseStandingAs(Core body, String at) {
        Core.Widen standing = assertInstanceOf(Core.Widen.class, body);
        assertEquals(Type.ref(declared(at)), standing.type());
        return assertInstanceOf(Core.Construct.class, standing.value()).typeName();
    }

    /**
     * A case written where its sum is taken stands as the sum: the definition's body is the case's
     * construction, widened to the parameter's type.
     */
    @Test
    void aCaseWrittenWhereItsSumIsTakenStandsAsTheSum() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertEquals(declared("Individual"), caseStandingAs(
                computingOnlyInput(row(program, "named", "an individual")).body(), "Orderer"));
    }

    /** A value given to an optional field is the optional, holding the case standing as the sum. */
    @Test
    void aValueGivenToAnOptionalFieldIsTheOptional() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        Core.Construct slot = assertInstanceOf(Core.Construct.class,
                computingOnlyInput(row(program, "slotted", "one held")).body());
        Core.OptionSome held = assertInstanceOf(Core.OptionSome.class,
                slot.values().getFirst().value());
        assertEquals(declared("Corporation"), caseStandingAs(held.value(), "Orderer"));
    }

    /**
     * A list of cases is the list its elements joined at, standing as the parameter's list.
     *
     * <p>Which is not each element standing as the sum. A list is elaborated from its elements up,
     * as it is in a body, and only the whole of it stands where the parameter takes it — a shape
     * an output rebuilding the value from what was observed would have had to guess, and could
     * guess otherwise.
     */
    @Test
    void aListOfCasesIsTheListTheyJoinedAtStandingAsTheParameters() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        Core.Widen standing = assertInstanceOf(Core.Widen.class,
                computingOnlyInput(row(program, "everyone", "both kinds")).body());
        assertEquals(Type.list(Type.ref(declared("Orderer"))), standing.type());
        Core.ListLit list = assertInstanceOf(Core.ListLit.class, standing.value());
        assertEquals(List.of(declared("Individual"), declared("Corporation")),
                list.elements().stream().map(it -> assertInstanceOf(Core.Construct.class,
                        Core.withoutStanding(it)).typeName()).toList());
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
        CheckedHelper computing = computingOnlyInput(row(program, "doubled", "two"));

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

        CheckedRow stood = row(program, "counted", "looked up");
        assertInstanceOf(CheckedRow.WithStandIns.class, stood.statement());
        assertInstanceOf(Core.Construct.class, computingOnlyInput(stood).body());

        CheckedRow owed = row(program, "lookUp", "owed");
        assertInstanceOf(CheckedRow.AnswerOwed.class, owed.statement());
        assertInstanceOf(Core.Construct.class, computingOnlyInput(owed).body());
    }

    /** Two rows writing the same value are two operands, and each is computed by its own. */
    @Test
    void eachOperandIsComputedByItsOwnDefinition() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertNotSame(computingOnlyInput(row(program, "doubled", "two")),
                computingOnlyInput(row(program, "counted", "looked up")));
    }

    /**
     * A row written in an attached file names the definition of its own operand, and not one of
     * the rows written before it in the module's source.
     *
     * <p>The definitions are numbered over every row the module has, wherever it is written, so a
     * reading that numbered one source's rows from nought would hand this row the module's first
     * operand — an individual, where it wrote a corporation.
     */
    @Test
    void aRowOfAnAttachedFileIsComputedByItsOwnOperand() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));

        CheckedHelper inline = computingOnlyInput(row(program, "named", "an individual"));
        CheckedHelper attached = computingOnlyInput(row(program, "named", "a corporation"));

        assertEquals(declared("Individual"), caseStandingAs(inline.body(), "Orderer"));
        assertEquals(declared("Corporation"), caseStandingAs(attached.body(), "Orderer"));
        assertNotSame(inline, attached);
    }
}
