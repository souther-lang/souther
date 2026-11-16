package souther.compiler.query;

import souther.compiler.ACompiledModel;

import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm whose way in compares a number with a written one and then with another value is offered
 * a row, whichever of the two comes first: its way in is held to what each guard asks, one after
 * another, and not to a point of the first that the second can rule out. An arm whose way in no
 * value takes is offered none.
 */
class AnArmEnteredThroughARelationAmongNumbersIsOfferedARowTest {

    /** Each arm a finding is raised for that is offered a row, as {@code fork/part}: the fork by
     *  the ordinal of its construct, the part 0 being the one taken on holding. */
    private static Set<String> armsOfferedARow(String model, String module) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.Findings(module)).value().stream()
                .filter(each -> each.about() instanceof About.AnArmNoRowGoesThrough)
                .filter(Adequacy.Finding::established)
                .map(each -> ((About.AnArmNoRowGoesThrough) each.about()).arm().place().arm())
                .map(arm -> arm.fork().origin().ordinal() + "/" + arm.part())
                .collect(Collectors.toCollection(TreeSet::new));
    }

    @Test
    void anArmAtOrOverALimitAndUnderAnotherValueIsOfferedARow() {
        // The inner `then` is the arm of the fork at 2 that is taken on holding, and the row for
        // it stands at or over 13 and under y.
        assertEquals(Set.of("0/0", "2/0", "2/1"), armsOfferedARow("""
                module example.arm

                behavior f : (x: Int, y: Int) -> Int

                let f (x, y) = if x >= 13 then (if x < y then 1 else 2) else 3

                example f
                    | (5, 1) -> 3
                """, "example.arm"));
    }

    @Test
    void anArmNoValueTakesIsOfferedNoRow() {
        // At or over 13 and under 5: the inner `then`, 2/0, is no arm a row is owed.
        assertEquals(Set.of("0/0", "2/1"), armsOfferedARow("""
                module example.armnone

                behavior f : (x: Int, y: Int) -> Int

                let f (x, y) = if x >= 13 then (if x < 5 then 1 else 2) else 3

                example f
                    | (5, 1) -> 3
                """, "example.armnone"));
    }
}
