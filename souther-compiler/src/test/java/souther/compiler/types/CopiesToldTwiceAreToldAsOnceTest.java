package souther.compiler.types;

import org.junit.jupiter.api.Test;

import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * What two values of copies say together is each copy once, in the order first met, and where one
 * of them says all of it that is the one.
 *
 * <p>A read that stands under two halves is told the same copies by both, so putting them together
 * is mostly putting a value with an equal one; a value put together again would have every copy
 * of it hashed again for nothing.
 */
class CopiesToldTwiceAreToldAsOnceTest {

    private static ModelOccurrence copy(int ordinal) {
        return new ModelOccurrence(SourceConstructOrigin.written(new WrittenOwner.Body("demo", "go"),
                ordinal, SourceConstruct.IF), ExpansionLineage.ORIGINAL);
    }

    private static ModelOccurrences of(int... ordinals) {
        return ModelOccurrences.of(Arrays.stream(ordinals).mapToObj(
                CopiesToldTwiceAreToldAsOnceTest::copy).toList());
    }

    @Test
    void aValuePutTogetherWithItselfIsThatValue() {
        ModelOccurrences ab = of(0, 1);
        assertSame(ab, ab.and(ab));
    }

    @Test
    void aValuePutTogetherWithOneEqualToItIsThatValue() {
        ModelOccurrences ab = of(0, 1);
        assertSame(ab, ab.and(of(0, 1)));
    }

    @Test
    void valuesThatDifferAreEachCopyOnceInTheOrderFirstMet() {
        List<ModelOccurrences> values = List.of(of(0, 1), of(1, 2), of(1, 0), of(2), of(0, 1, 2),
                ModelOccurrences.NONE);
        for (ModelOccurrences first : values) {
            for (ModelOccurrences second : values) {
                Set<ModelOccurrence> held = new LinkedHashSet<>(first.inOrder());
                held.addAll(second.inOrder());
                assertEquals(List.copyOf(held), first.and(second).inOrder(),
                        first + " and " + second);
            }
        }
    }
}
