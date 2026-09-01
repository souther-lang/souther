package souther.compiler.observe;

import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What a row states is what the row wrote, whether or not anything applied the behavior.
 *
 * <p>A row is written down before anything runs it, and what it hands over — what stands in for each
 * dependency, the inputs, the expectation — is the same text either way. A snapshot whose rows said
 * one thing where this compile found an implementation and another where it did not would be
 * publishing the compile rather than the program: the same source, read twice, would hand two
 * different obligations to two outputs.
 *
 * <p>Kept two ways, and the first is not a rule to remember. {@link RowStatements} is in
 * {@code observe}, and what a run found to apply a behavior with is private to {@code examples},
 * which this package may not name — so the reading cannot ask. What is left to check here is that
 * nothing is handed it either: a caller can carry an answer across a boundary the compiler keeps by
 * putting it in an argument, and a {@code boolean} saying whether anything applies the behavior
 * would be exactly that.
 */
class WhatARowStatesDoesNotDependOnWhatAppliedTheBehaviorTest {

    /**
     * What making a statement takes, said out loud.
     *
     * <p>Reflection and not a reading of the source, because what a caller can hand over is the
     * signature the compiler produced. A parameter added here is a line to change with a reason
     * beside it — and the reason cannot be that a statement wants to know what this compile could
     * run, which is what this list exists to make hard to write.
     */
    @Test
    void whatMakingAStatementTakesIsTheRowAndNothingElse() {
        List<String> takes = new ArrayList<>();
        for (Method method : RowStatements.class.getDeclaredMethods()) {
            if (!Modifier.isPublic(method.getModifiers())) {
                continue;
            }
            List<String> parameters = new ArrayList<>();
            for (Class<?> parameter : method.getParameterTypes()) {
                parameters.add(parameter.getSimpleName());
            }
            takes.add(method.getName() + parameters);
        }
        // Sorted, because what order the methods come back in is not answered for: a second one
        // added here would make the list depend on the run rather than on what was declared.
        takes.sort(Comparator.naturalOrder());

        assertEquals(List.of("read[List, List, Expectation]"), takes,
                "what a row states is made of what was read of the row");
    }

    /**
     * And a row of a behavior nothing implements states what stood in for its dependencies.
     *
     * <p>Nothing applies {@code rateOf} here — it is declared and never written — so this row is one
     * no run reached. It states its stand-in all the same, because the {@code fake} beside it is
     * what the row was written to run against and that is true of the text rather than of the run.
     */
    @Test
    void aRowOfABehaviorNothingAppliesStatesWhatStandsInForIt() {
        CheckedProgram program = CheckedProgram.of(List.of("""
                module demo

                data Price = Int
                data Rate = Int

                behavior rateFor : (of: Price) -> Rate

                behavior rateOf : (base: Price) -> Rate
                    depends on rateFor

                fake rateFor
                    | (Price(1)) -> Rate(10)

                example rateOf
                    | "the one price it lists" : (Price(1)) -> Rate(10)
                """));

        CheckedBehavior rateOf =
                program.module("demo").behavior(new ValueName.Behavior("demo", "rateOf"));
        CheckedRow.WithStandIns states = assertInstanceOf(CheckedRow.WithStandIns.class,
                rateOf.rows().get(0).statement(),
                "a row states its stand-ins whether or not anything was found to run it");

        assertEquals(new ValueName.Behavior("demo", "rateFor"),
                states.standsIn().get(0).dependency());
        assertEquals(1, states.standsIn().get(0).stated().entries().size(),
                "and the entries the table states are the ones it was written with");
    }
}
