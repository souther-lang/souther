package souther.compiler.query;

import souther.compiler.check.AnalysisBody;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.TermPath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a call of a behavior stands in its caller's input is read off the body, and the element a
 * fold hands the call is the element of the list the caller takes.
 */
class ACallInAFoldStandsAtTheElementOfTheListTest {

    private static final String MODEL = """
            module repro.split

            data Pin = Int
                invariant value >= 1 && value <= 12

            data Throw = List<Pin>
                invariant List.allDistinctBy(p -> p, value)

            behavior points : (t: Throw) -> Int

            let points (t) = List.length(t.value)

            example points
                | (Throw([])) -> 0

            behavior score : (throws: List<Throw>) -> Int

            let score (throws) = List.fold((acc, t) -> acc + points(t), 0, throws)
            """;

    @Test
    void theElementOfAFoldIsWhereTheListHoldsIt() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Db db = compilation.db();
        var spec = Adequacy.specOf(db.ask(new Shapes.CheckSurface("repro.split")).value(), "score");
        InputReading input = Adequacy.inputReadingOf(db, "repro.split", spec);
        AnalysisBody analysis = db.ask(new Bodies.Observable("repro.split")).value()
                .analysisBodies().get("score");

        List<CallExampleSeeds.Call> calls = CallExampleSeeds.callsIn(analysis, input, _ -> true);

        List<Optional<TermPath>> at = calls.stream()
                .filter(call -> call.callee().name().equals("points"))
                .map(call -> call.at().getFirst())
                .toList();
        assertEquals(1, at.size(), () -> "one call of points: " + calls);
        assertEquals("throws[*]", at.getFirst().map(Object::toString).orElse("none"));
    }
}
