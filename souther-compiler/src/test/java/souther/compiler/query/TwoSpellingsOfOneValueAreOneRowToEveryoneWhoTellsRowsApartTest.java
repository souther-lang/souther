package souther.compiler.query;

import souther.compiler.partition.ComposedRow;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * The questions "is this the row already offered" and "was this row already run" are answered by
 * what the row puts in, never by how the generator happened to spell it.
 *
 * <p>The templates here are given a meaning by hand, so this fixes only that the comparison reads
 * the meaning. That the meaning is the value written out is fixed against the module's own decoder
 * by {@link NoTwoOfferedRowsPutInTheSameValuesTest} and by
 * {@code ATemplateWrittenAgainstAStatedValueMeansTheValueItBuildsTest}.
 */
class TwoSpellingsOfOneValueAreOneRowToEveryoneWhoTellsRowsApartTest {

    private static final FixtureTemplate BY_NAME =
            FixtureTemplate.integer(7).meaningAs("Hit(0)");

    private static final FixtureTemplate WRITTEN_OUT = FixtureTemplate.integer(0).meaningAs("Hit(0)");

    private static final FixtureTemplate ANOTHER_VALUE = FixtureTemplate.integer(1);

    private static Generator.GeneratedRow row(FixtureTemplate... inputs) {
        return new Generator.GeneratedRow(List.of(new Generator.Purpose.Unstated()),
                List.of(inputs), List.of());
    }

    @Test
    void rowsPuttingInTheSameValueAreOneKeyAndShowTheSpellingComposedFirst() {
        RowKey named = RowKey.of("f", row(BY_NAME));
        RowKey writtenOut = RowKey.of("f", row(WRITTEN_OUT));
        assertEquals(named, writtenOut);
        assertEquals(named.hashCode(), writtenOut.hashCode());
        assertEquals("7", named.inputs());
        assertEquals("0", writtenOut.inputs());
    }

    @Test
    void rowsPuttingInDifferentValuesAreTwoKeys() {
        assertNotEquals(RowKey.of("f", row(WRITTEN_OUT)), RowKey.of("f", row(ANOTHER_VALUE)));
    }

    @Test
    void theSameValueUnderTwoBehaviorsIsTwoKeys() {
        assertNotEquals(RowKey.of("f", row(WRITTEN_OUT)), RowKey.of("g", row(WRITTEN_OUT)));
    }

    @Test
    void aRowIsTheSameLineAndTheSameRunWhateverItsValuesWereSpelledAs() {
        assertEquals(new ComposedRow(List.of(BY_NAME), List.of()).identity(),
                new ComposedRow(List.of(WRITTEN_OUT), List.of()).identity());
        assertNotEquals(new ComposedRow(List.of(WRITTEN_OUT), List.of()).identity(),
                new ComposedRow(List.of(ANOTHER_VALUE), List.of()).identity());
    }
}
