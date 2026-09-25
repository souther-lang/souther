package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.observe.RowIdentity;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.program.StandsIn;
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
 * What an output answers a dependency with when it runs a row: the definition computing each value
 * the row's stand-in states, elaborated where the dependency takes or answers it.
 *
 * <p>The values a stand-in states are observations, as a row's inputs are, and an observation does
 * not say how the value stands where it is handed over. A case written where the dependency takes
 * or answers its sum stands as the sum, and a value given to an optional field is the optional. What
 * crosses for each is the definition the module already holds for the value as written, so an
 * output answering the dependency in code of its own does not decide either again.
 */
class AStandInsValuesAreTheDefinitionsComputingThemTest {

    private static final String MODULE = """
            module orders

            data Individual = { name: String }
            data Corporation = { company: String }
            data Orderer = Individual | Corporation

            data Retail = { rate: Int }
            data Wholesale = { rate: Int }
            data Tier = Retail | Wholesale

            behavior tierOf : (orderer: Orderer) -> Tier

            behavior rateFor : (orderer: Orderer) -> Int
                depends on tierOf
            let rateFor (orderer, tierOf) = match tierOf(orderer) with
                | Retail as r -> r.rate
                | Wholesale as w -> w.rate

            data Link = { partner: Orderer? }

            behavior partnerOf : (orderer: Orderer) -> Link

            behavior partnered : (orderer: Orderer) -> Int
                depends on partnerOf
            let partnered (orderer, partnerOf) = match partnerOf(orderer).partner with
                | Some p -> 1
                | None -> 0

            fake tierOf
                | (Individual { name = "ada" }) -> Retail { rate = 1 }
                | (Individual { name = "cy" }) -> Wholesale { rate = 5 }
                | _ -> Wholesale { rate = 2 }

            example rateFor
                | "listed" : (Individual { name = "ada" }) -> 1
                | "owed" : (Individual { name = "cy" }) -> <?>
                | "the rest" : (Corporation { company = "acme" }) -> 2
                | "on the row" : (Corporation { company = "acme" }) with tierOf = Retail { rate = 3 } -> 3

            example partnered
                | "ada's" : (Individual { name = "ada" }) -> 1
            """;

    /** Rows and a table of the same module written in a file of their own, after the module's. */
    private static final String ATTACHED = """
            examples for orders

            fake partnerOf
                | (Individual { name = "ada" }) -> Link { partner = Corporation { company = "acme" } }

            example rateFor
                | "on an attached row" : (Individual { name = "bob" }) with tierOf = Wholesale { rate = 4 } -> 4
            """;

    private static TypeSymbol.AtModule declared(String name) {
        return TypeSymbols.declared(new TypeKey("orders", name));
    }

    private static StandsIn standingIn(CheckedProgram program, String behavior, String named) {
        CheckedBehavior of = program.module("orders")
                .behavior(new ValueName.Behavior("orders", behavior));
        CheckedRow row = of.rows().stream()
                .filter(it -> it.identity().equals(new RowIdentity.Named(named)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + named + "` among " + of.rows()));
        List<StandsIn> standsIn = switch (row.statement()) {
            case CheckedRow.WithStandIns it -> it.standsIn();
            case CheckedRow.AnswerOwed it -> it.standsIn();
            case CheckedRow.SelfContained _, CheckedRow.NotReproducible _ ->
                    throw new AssertionError(row + " is " + row.statement());
        };
        assertEquals(1, standsIn.size(), () -> "what stands in for " + row + " is " + standsIn);
        return standsIn.getFirst();
    }

    private static CheckedHelper computingTheRest(StandsIn standsIn) {
        return assertInstanceOf(StandsIn.Otherwise.Answers.class, standsIn.otherwise(),
                () -> standsIn + " answers nothing for the rest").definition();
    }

    /** The case a definition's body builds, standing as {@code at}. */
    private static TypeSymbol.AtModule caseStandingAs(Core body, String at) {
        Core.Widen standing = assertInstanceOf(Core.Widen.class, body);
        assertEquals(Type.ref(declared(at)), standing.type());
        return assertInstanceOf(Core.Construct.class, standing.value()).typeName();
    }

    /**
     * An entry's argument written as a case stands as the sum the dependency takes, and its answer
     * as the sum the dependency answers.
     */
    @Test
    void anEntrysValuesStandWhereTheDependencyTakesAndAnswersThem() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        StandsIn standsIn = standingIn(program, "rateFor", "listed");

        StandsIn.Entry entry = standsIn.entries().getFirst();
        assertEquals(standsIn.stated().entries(),
                standsIn.entries().stream().map(StandsIn.Entry::stated).toList(),
                "the entries are the ones the stand-in states, in its order");
        assertEquals(declared("Individual"),
                caseStandingAs(entry.argumentDefinitions().getFirst().body(), "Orderer"));
        assertEquals(declared("Retail"), caseStandingAs(entry.answerDefinition().body(), "Tier"));
    }

    /**
     * Each entry is computed by the definitions of the row it is, and not of the row beside it: the
     * table lists two, answering different cases.
     */
    @Test
    void eachEntryIsComputedByTheDefinitionsOfItsOwnRow() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        List<StandsIn.Entry> entries = standingIn(program, "rateFor", "listed").entries();

        assertEquals(List.of(declared("Retail"), declared("Wholesale")),
                entries.stream().map(it -> caseStandingAs(it.answerDefinition().body(), "Tier"))
                        .toList());
    }

    /**
     * A row whose answer is owed hands over what stands in for its dependency as a row stating one
     * does: an output running it to find the answer runs it against what the row states the
     * dependency answers.
     */
    @Test
    void aRowWhoseAnswerIsOwedHandsOverWhatStandsIn() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        CheckedRow owed = program.module("orders")
                .behavior(new ValueName.Behavior("orders", "rateFor")).rows().stream()
                .filter(it -> it.identity().equals(new RowIdentity.Named("owed")))
                .findFirst().orElseThrow();
        assertInstanceOf(CheckedRow.AnswerOwed.class, owed.statement());
        StandsIn standsIn = standingIn(program, "rateFor", "owed");

        assertEquals(List.of(declared("Retail"), declared("Wholesale")),
                standsIn.entries().stream()
                        .map(it -> caseStandingAs(it.answerDefinition().body(), "Tier")).toList());
        assertEquals(declared("Wholesale"),
                caseStandingAs(computingTheRest(standsIn).body(), "Tier"));
    }

    /** What a table answers for the rest is computed by the definition of its {@code _} row. */
    @Test
    void theAnswerForTheRestIsTheDefaultRowsDefinition() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));

        assertEquals(declared("Wholesale"),
                caseStandingAs(computingTheRest(standingIn(program, "rateFor", "the rest")).body(),
                        "Tier"));
    }

    /**
     * A {@code with} lists nothing and answers everything, and what computes that answer is the
     * definition of the value it writes — not the table beside it, which the row does not run
     * against.
     */
    @Test
    void aWithIsComputedByTheValueItWrites() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        StandsIn standsIn = standingIn(program, "rateFor", "on the row");

        assertEquals(List.of(), standsIn.entries());
        assertEquals(declared("Retail"), caseStandingAs(computingTheRest(standsIn).body(), "Tier"));
    }

    /**
     * A value given to an optional field of what a dependency answers is the optional, holding the
     * case standing as the sum; and a table with no {@code _} row states nothing for the rest, so
     * nothing computes it.
     *
     * <p>The table is written in the attached file and the row in the module's: what a module's
     * rows run against is every table the module writes, wherever it is written.
     */
    @Test
    void aValueGivenToAnOptionalFieldOfTheAnswerIsTheOptional() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        StandsIn standsIn = standingIn(program, "partnered", "ada's");

        Core.Construct link = assertInstanceOf(Core.Construct.class,
                standsIn.entries().getFirst().answerDefinition().body());
        Core.OptionSome partner = assertInstanceOf(Core.OptionSome.class,
                link.values().getFirst().value());
        assertEquals(declared("Corporation"), caseStandingAs(partner.value(), "Orderer"));
        assertInstanceOf(StandsIn.Otherwise.NothingStated.class, standsIn.otherwise());
    }

    /**
     * Each definition is one the module holds, and a row of an attached file names the one for the
     * value it writes rather than one of the values the module's source writes before it.
     *
     * <p>The definitions are numbered over every row and table the module has, wherever it is
     * written, so a reading that numbered one source's from nought would hand the attached row a
     * value of the module's source.
     */
    @Test
    void eachValueIsComputedByTheModulesDefinitionForIt() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));
        CheckedModule module = program.module("orders");

        CheckedHelper inline = computingTheRest(standingIn(program, "rateFor", "on the row"));
        CheckedHelper attached =
                computingTheRest(standingIn(program, "rateFor", "on an attached row"));
        StandsIn.Entry entry = standingIn(program, "rateFor", "listed").entries().getFirst();

        for (CheckedHelper each : List.of(inline, attached, entry.answerDefinition(),
                entry.argumentDefinitions().getFirst())) {
            assertTrue(module.helpers().stream().anyMatch(it -> it == each),
                    () -> each + " is not among " + module.helpers());
        }
        assertEquals(declared("Wholesale"), caseStandingAs(attached.body(), "Tier"));
        assertNotSame(inline, attached);
    }
}
