package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A statement over {@code hs[*]} says of {@code hs} that it holds that element, so {@code hs} as a
 * position is not left unread where its element is. A coordinate that names a number of {@code hs}
 * is another thing: the filing keeps which number each is, and only a position is taken for the
 * container.
 */
class TheContainerPositionOfAnElementIsLeftOutAndNoOtherCoordinateTest {

    private static final TermPath CONTAINER = TermPath.of("hs");
    private static final TermPath ELEMENT = CONTAINER.element();

    @Test
    void aPositionIsLeftOutWhereAnElementOfItIsFiledAndANumberOfItIsNot() {
        FilingCoordinate element = FilingCoordinate.of(new NumericTerm.ValueOf(ELEMENT));
        FilingCoordinate container = FilingCoordinate.at(CONTAINER);
        FilingCoordinate numberOfContainer = FilingCoordinate.of(new NumericTerm.ValueOf(CONTAINER));

        assertEquals(List.of(element, numberOfContainer),
                GuardThresholds.withoutTheContainerPositionsOfTheirElements(
                        List.of(element, container, numberOfContainer)));
    }

    @Test
    void aPositionStaysWhereNoElementOfItIsFiled() {
        FilingCoordinate container = FilingCoordinate.at(CONTAINER);
        FilingCoordinate other = FilingCoordinate.at(TermPath.of("ns").element());

        assertEquals(List.of(other, container),
                GuardThresholds.withoutTheContainerPositionsOfTheirElements(
                        List.of(other, container)));
    }
}
