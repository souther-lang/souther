package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.meta.ModulePath;
import souther.compiler.observe.ArmObservation;
import souther.compiler.report.GeneratedRows;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A compilation evaluates a module as one program, whatever reads it.
 *
 * <p>Its rows, the tables its fakes state, what its statements say of each other, the values a search
 * builds and the rows a search tries are all run against the program this compilation evaluates the
 * module as. A reading that named the other one would have the whole module generated a second time,
 * fixtures and all, for classes that differ from the first only in calls that do nothing outside a
 * recording.
 *
 * <p>The model reaches every one of those readings: a table and a row recorded for the behavior it
 * stands in for, so their statements are compared, and a row for the behavior that depends on it, so
 * a search builds values and tries rows.
 */
class AModuleIsEvaluatedAsOneProgramPerCompilationTest {

    private static final String MODEL = """
            module probe.once

            behavior lookup : (key: Int) -> Int

            behavior top : (a: Int) -> Int
                depends on lookup
            let top (a, lookup) = if lookup(a) > 10 then a else 0

            fake lookup
                | (1) -> 20

            example lookup
                | "the one the table states" : (1) -> 20

            example top
                | "past ten" : (1) -> 1
            """;

    @Test
    void aMeasuredCompilationGeneratesOnlyTheProgramThatRecords() {
        assertEquals(List.of(ArmObservation.RECORD), programsGenerated(true));
    }

    @Test
    void aCompilationThatMeasuresNothingGeneratesOnlyTheOneThatDoesNot() {
        assertEquals(List.of(ArmObservation.OMIT), programsGenerated(false));
    }

    /** Which of the two programs of the module the compilation generated, having read it every way. */
    private static List<ArmObservation> programsGenerated(boolean measured) {
        Compilation compilation = Compilation.ofSources(List.of(MODEL), ModulePath.EMPTY);
        if (measured) {
            compilation.measure(Adequacy.Asked.fullReport());
        }
        ACompiledModel.compiles(compilation);
        compilation.answerEverything();
        if (measured) {
            GeneratedRows.offered(compilation, "probe.once", "top");
        }
        Db db = compilation.db();
        return List.of(ArmObservation.values()).stream()
                .filter(arms -> db.isComputed(new Output.EvaluationLinked("probe.once", arms)))
                .toList();
    }
}
