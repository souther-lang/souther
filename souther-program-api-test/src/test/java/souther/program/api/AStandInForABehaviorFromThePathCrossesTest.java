package souther.program.api;

import souther.compiler.Compiler;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Verdict;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.program.StandsIn;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A row stood in for by a behavior another compile declared crosses like any other.
 *
 * <p>What a behavior depends on is not always something the module the row is written in declares,
 * and not always something this compile read the source of: a published module exposes an injected
 * behavior, and a module importing it stands in for it while its own rows run. What the row states
 * of that stand-in is the same fact whichever of the two the dependency was declared in.
 *
 * <p>Two source modules compiled together do not say this. Both are among what a snapshot is taken
 * of, so anything the snapshot works out for itself about a dependency is there to be found; a
 * dependency declared only on the path is what says whether what a stand-in states came from the
 * reading that built it.
 */
class AStandInForABehaviorFromThePathCrossesTest {

    /** Published by another project: a type and a behavior nothing there implements. */
    private static final String PUBLISHED = """
            module lib.rates exposing ( Rate, rateFor )
            data Rate = Int
            behavior rateFor : (of: Int) -> Rate
            """;

    private static final String USES = """
            module app.uses
            import lib.rates ( Rate, rateFor )

            data Price = Int

            behavior rateOf : (base: Price) -> Rate
                depends on rateFor

            let rateOf (base, rateFor) = rateFor(base.value)

            fake rateFor
                | (1) -> Rate(10)
                | _ -> Rate(99)

            example rateOf
                | "a base the table lists" : (Price(1)) -> Rate(10)
                | "one it does not" : (Price(7)) -> Rate(99)
            """;

    @Test
    void aDependencyDeclaredOnlyOnThePathIsStoodInForAcrossTheBoundary() {
        Map<String, ClassFileImage> published = Compiler.compile(PUBLISHED);
        CheckedProgram program = CheckedProgram.of(List.of(USES), ModulePath.of(published));

        List<CheckedRow> rows = program.module("app.uses")
                .behavior(new ValueName.Behavior("app.uses", "rateOf")).rows();
        assertEquals(2, rows.size(), () -> "the rows that crossed are " + rows);

        for (CheckedRow row : rows) {
            CheckedRow.WithStandIns states =
                    assertInstanceOf(CheckedRow.WithStandIns.class, row.statement(),
                            () -> row + " stands in for a behavior another compile declared");
            StandsIn rateFor = states.standsIn().get(0);
            assertEquals(new ValueName.Behavior("lib.rates", "rateFor"), rateFor.dependency(),
                    "the dependency is the declaration it is, in the module that declares it");
            assertEquals(1, rateFor.stated().takes().size(),
                    "and what it takes came from the signature the table was built against");

            // The behavior hands the number inside its input straight on, so what the stand-in
            // answers for that number is what the row was held against when it ran.
            ObservedValue price = states.states().inputs().get(0);
            StandsIn.Answer answered = rateFor.answering(
                    List.of(assertInstanceOf(ObservedValue.Constructed.class, price).field("value")));
            StandsIn.Answer.TheValue value =
                    assertInstanceOf(StandsIn.Answer.TheValue.class, answered,
                            () -> rateFor + " answered nothing for " + row);
            assertEquals(new Verdict.Held(), states.holds(value.value()),
                    () -> "what " + rateFor + " answers for " + row + " is not what the row was"
                            + " held against when it ran");
        }
    }
}
