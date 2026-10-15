package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The element of a container a name every case of a sum spreads holds is read at the name, as the
 * name itself is.
 *
 * <p>{@code e.tags} stands under each case, and so does each of its elements; a condition reads
 * the element at the name. What the element's type says of it holds under whichever case the row
 * is, so the reading of the input names it there, a relation over it is one a region carries, and
 * a line drawn on it is filed at the element under each case.
 */
class AnElementOfAContainerEveryCaseSpreadsIsReadAtTheNameTest {

    private static final String MODEL = """
            module probe.spread

            data Common = { tags: List<Int> }
            data First = { ...Common, x: Int }
            data Second = { ...Common, y: Int }
            data Either = First | Second

            data A
            data B

            behavior f : (e: Either) -> A | B
            let f (e) = if List.any(t -> t > 3, e.tags) then A else B

            data Shared = { marks: List<Int> }
            data Sprig = { ...Shared, size: Int }
            data Limb = { ...Shared, under: Wood }
            data Wood = Sprig | Limb

            behavior g : (w: Wood) -> A | B
            let g (w) =
                match w with
                    | Sprig -> B
                    | Limb { under } -> if List.any(m -> m > 3, under.marks) then A else B
            """;

    private static final Compilation COMPILATION = compiled();

    private static Compilation compiled() {
        Compilation made = Compilation.ofSource(MODEL, "Main");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        return made;
    }

    @Test
    void aRelationOverTheElementAtTheNameIsOneARegionCarries() {
        InputDomain inputs = COMPILATION.db().ask(new Adequacy.Inputs("probe.spread")).value()
                .get("f");
        assertNotNull(inputs, "the model compiles");
        LinearForm<NumericTerm> above = LinearForm.atomMinusConstant(
                new NumericTerm.ValueOf(TermPath.of("e").then("tags").element()),
                ExactRatio.of(3));
        assertInstanceOf(SearchRegion.Assumption.Taken.class,
                inputs.quantities(RuleReadings.of(COMPILATION, "probe.spread")).region()
                        .assuming(above, Rel.GT),
                "the element at the name is named by the rules of the element");
    }

    /**
     * And where the name is under a value the reading of the input stopped unfolding — a sum
     * reached again inside one of its own cases — the condition naming it is what takes the
     * reading under each case, and so to the element there.
     */
    @Test
    void anElementUnderAValueReachedAgainIsReadAtTheNameAsWell() {
        List<Axis> axes = COMPILATION.db().ask(new Adequacy.Divided("probe.spread", "g")).value()
                .axes();
        List<Axis> marks = axes.stream()
                .filter(each -> each.path().toString().endsWith("under@Limb.marks[*]")
                        || each.path().toString().endsWith("under@Sprig.marks[*]"))
                .toList();
        assertEquals(2, marks.size(), () -> "the element under each case of the value reached"
                + " again: " + axes.stream().map(each -> each.path().toString()).toList());
        marks.forEach(axis -> assertTrue(axis.classes().size() > 1,
                () -> "the line at three divides it: " + axis));
    }

    @Test
    void aLineOnTheElementIsFiledAtTheElementUnderEachCase() {
        assertEquals(List.of(), COMPILATION.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        List<Axis> axes = COMPILATION.db().ask(new Adequacy.Divided("probe.spread", "f")).value()
                .axes();
        for (String at : List.of("e@First.tags[*]", "e@Second.tags[*]")) {
            Axis axis = axes.stream().filter(each -> each.path().toString().equals(at))
                    .findFirst().orElseThrow(() -> new AssertionError(
                            "a measure at " + at + " among " + axes.stream()
                                    .map(each -> each.path().toString()).toList()));
            assertTrue(axis.classes().size() > 1,
                    () -> "the line at three divides the element under this case: " + axis);
        }
    }
}
