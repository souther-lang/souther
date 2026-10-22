package souther.program.api;

import souther.compiler.core.Core;
import souther.compiler.observe.RowIdentity;
import souther.compiler.program.CheckedAssertion;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedHelper;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
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
 * What a row states of the answer reaches an output as something it compiles, as the row's inputs
 * do: the definition computing a stated value, or the case a row states and nothing under it.
 *
 * <p>An output whose answer never comes back to the JVM — an implementation run by a host's own test
 * runner — holds the answer where it is, and is handed nothing to hold it with unless the stated
 * value crosses as a computation. A computation of its own, built from what the row was observed to
 * state, would be the elaboration worked out a second time outside the checker.
 */
class WhatARowStatesOfTheAnswerIsHandedOverAsAComputationTest {

    private static final String MODULE = """
            module orders

            data Receipt = { total: Int }
            data Found = { v: Int }
            data Missing

            behavior receiptOf : (n: Int) -> Receipt

            behavior find : (n: Int) -> Found | Missing

            behavior lookUp : (n: Int) -> Int

            behavior counted : (n: Int) -> Int
                depends on lookUp
            let counted (n, lookUp) = lookUp(n) + 1

            fake lookUp
                | (2) -> 10

            example receiptOf
                | "three" : (3) -> Receipt { total = 3 }

            example find
                | "found" : (1) -> Found
                | "missing" : (2) -> Missing

            example counted
                | "looked up" : (2) -> 11

            example lookUp
                | "owed" : (3) -> <?>

            behavior pick : (n: Int) -> Int | Missing

            example pick
                | "a number" : (1) -> 1
                | "missing" : (2) -> Missing
            """;

    /** Rows of the same module written in a file of their own, after the module's. */
    private static final String ATTACHED = """
            examples for orders

            example receiptOf
                | "five" : (5) -> Receipt { total = 5 }
            """;

    private static CheckedRow row(CheckedProgram program, String behavior, String named) {
        CheckedBehavior of = program.module("orders")
                .behavior(new ValueName.Behavior("orders", behavior));
        return of.rows().stream()
                .filter(it -> it.identity().equals(new RowIdentity.Named(named)))
                .findFirst()
                .orElseThrow(() -> new AssertionError("no row `" + named + "` among " + of.rows()));
    }

    private static CheckedAssertion assertionOf(CheckedRow row) {
        return switch (row.statement()) {
            case CheckedRow.SelfContained it -> it.assertion();
            case CheckedRow.WithStandIns it -> it.assertion();
            case CheckedRow.AnswerOwed it ->
                    throw new AssertionError("the row owes its answer: " + it);
            case CheckedRow.NotReproducible it ->
                    throw new AssertionError("the row states no values: " + it.why());
        };
    }

    private static List<CheckedHelper> inputsOf(CheckedRow row) {
        return switch (row.statement()) {
            case CheckedRow.SelfContained it -> it.inputDefinitions();
            case CheckedRow.WithStandIns it -> it.inputDefinitions();
            case CheckedRow.AnswerOwed it -> it.inputDefinitions();
            case CheckedRow.NotReproducible it ->
                    throw new AssertionError("the row states no values: " + it.why());
        };
    }

    private static TypeSymbol.AtModule declared(String name) {
        return TypeSymbols.declared(new TypeKey("orders", name));
    }

    /**
     * A stated value is computed by a definition the module holds — the one this compiler ran to
     * compare the row — so what its body can end with is what the program answers for it, and it
     * builds the value the row wrote.
     */
    @Test
    void aStatedValueIsComputedByADefinitionTheModuleHolds() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedModule module = program.module("orders");
        CheckedRow three = row(program, "receiptOf", "three");

        CheckedHelper computing = assertInstanceOf(CheckedAssertion.Value.class,
                assertionOf(three)).computing();

        assertTrue(module.helpers().stream().anyMatch(it -> it == computing),
                () -> computing + " is not among " + module.helpers());
        assertEquals(declared("Receipt"),
                assertInstanceOf(Core.Construct.class, computing.body()).typeName());
        assertNotSame(inputsOf(three).getFirst(), computing,
                "what the row hands over and what it states are two operands");
    }

    /** A row stating a case and nothing under it is handed the case, whether or not it holds
     *  anything: there is no value to compute. */
    @Test
    void aStatedCaseIsTheCase() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertEquals(new CheckedAssertion.Case(declared("Found")),
                assertionOf(row(program, "find", "found")));
        assertEquals(new CheckedAssertion.Case(declared("Missing")),
                assertionOf(row(program, "find", "missing")));
    }

    /**
     * A row written in an attached file is handed the definition of its own stated value, and not
     * one of the rows written before it in the module's source: the definitions are numbered over
     * every row the module has, wherever it is written.
     */
    @Test
    void aRowOfAnAttachedFileIsHandedWhatComputesItsOwnStatedValue() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE, ATTACHED));

        CheckedHelper inline = assertInstanceOf(CheckedAssertion.Value.class,
                assertionOf(row(program, "receiptOf", "three"))).computing();
        CheckedHelper attached = assertInstanceOf(CheckedAssertion.Value.class,
                assertionOf(row(program, "receiptOf", "five"))).computing();

        assertEquals(3L, totalBuiltBy(inline));
        assertEquals(5L, totalBuiltBy(attached));
        assertNotSame(inline, attached);
    }

    private static long totalBuiltBy(CheckedHelper computing) {
        Core.Construct receipt = assertInstanceOf(Core.Construct.class, computing.body());
        return assertInstanceOf(Core.Int.class, receipt.values().getFirst().value()).value();
    }

    /**
     * Where the answer is a union with a scalar among its members, a row stating a case is handed the
     * case, and one stating a number the value.
     */
    @Test
    void aUnionWithAScalarHandsOverACaseAsACaseAndANumberAsAValue() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        assertEquals(new CheckedAssertion.Case(declared("Missing")),
                assertionOf(row(program, "pick", "missing")));
        assertInstanceOf(CheckedAssertion.Value.class, assertionOf(row(program, "pick", "a number")));
    }

    /** A row that needs something stood in for states its answer the same way. */
    @Test
    void aRowWithStandInsIsHandedWhatComputesItsStatedValue() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));
        CheckedRow stood = row(program, "counted", "looked up");

        assertInstanceOf(CheckedRow.WithStandIns.class, stood.statement());
        CheckedHelper computing = assertInstanceOf(CheckedAssertion.Value.class,
                assertionOf(stood)).computing();
        assertTrue(program.module("orders").helpers().stream().anyMatch(it -> it == computing),
                () -> computing + " is not among the module's helpers");
    }
}
