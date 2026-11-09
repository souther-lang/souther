package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.TestDay;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Shape;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A list is its elements in an order, and an order is a value of it: a statement may read the
 * first. So a listing that says it is every value of a list holds each order the elements may
 * stand in, and a set, which has none, holds each choice of them once.
 */
class AContainerPartIsListedAtEveryOrderItsElementsMayStandInTest {

    private static final RuleReadingSource RULES = RuleReadings.ofSource("module p\n");

    private static final RuleReadingContext READING =
            RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES, TestDay.TODAY);

    private static final TermPath AT = TermPath.of("o");

    private static ValuesOfAnElement.Listed listed(Type type, int most, int size) {
        return ValuesOfAnElement.of(type, AT, READING, most, (at, view) ->
                view.shape() instanceof Shape.Sequence
                        ? List.of(new ObservedValue.Integer(size)) : null);
    }

    private static List<List<Boolean>> flags(ValuesOfAnElement.Listed listed) {
        List<List<Boolean>> out = new ArrayList<>();
        for (ObservedValue each : listed.values()) {
            List<Boolean> one = new ArrayList<>();
            for (ObservedValue flag : ((ObservedValue.Sequence) each).elements()) {
                one.add(((ObservedValue.Bool) flag).value());
            }
            out.add(one);
        }
        return out;
    }

    @Test
    void aListOfTwoIsListedAtEachOrderOfItsElements() {
        ValuesOfAnElement.Listed listed = listed(Type.list(Type.BOOL), 256, 2);
        assertTrue(listed.all());
        assertEquals(List.of(List.of(false, false), List.of(false, true),
                List.of(true, false), List.of(true, true)), flags(listed));
    }

    @Test
    void aSetOfTwoIsListedAtEachChoiceOfItsElementsOnce() {
        ValuesOfAnElement.Listed listed = listed(Type.set(Type.BOOL), 256, 2);
        assertTrue(listed.all());
        assertEquals(List.of(List.of(false, true)), flags(listed));
    }

    @Test
    void aListingTheFigureStoppedIsNotEveryValue() {
        assertFalse(listed(Type.list(Type.BOOL), 3, 2).all());
    }
}
