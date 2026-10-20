package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static souther.compiler.reading.ReadInteractions.read;
import static souther.compiler.reading.ReadInteractions.shape;

/**
 * A total over the elements of a list written out consumes the choices each element makes into one
 * value, as {@code +} does between two of them. The list that holds them is no meeting: it is where
 * the values are kept, and the operation that adds them is where one is made of them.
 */
class ATotalOverChoicesIsAMeetingOfThemTest {

    private static final String PLUS = """
            module example.plus

            behavior total : (a: Bool, b: Bool) -> Int

            let total (a, b) = (if a then 100 else 0) + (if b then 200 else 0)
            """;

    private static final String SUM_OF_CHOICES = """
            module example.sumofchoices

            behavior total : (a: Bool, b: Bool) -> Int

            let total (a, b) = List.sum([ if a then 100 else 0, if b then 200 else 0 ])
            """;

    private static final String SUM_OF_ONE = """
            module example.sumofone

            behavior total : (a: Bool) -> Int

            let total (a) = List.sum([ if a then 100 else 0 ])
            """;

    private static final String LENGTH_OF_CHOICES = """
            module example.lengthofchoices

            behavior count : (a: Bool, b: Bool) -> Int

            let count (a, b) = List.length([ if a then 100 else 0, if b then 200 else 0 ])
            """;

    private static final String LIST_OF_CHOICES = """
            module example.listofchoices

            behavior pick : (a: Bool, b: Bool) -> List<Int>

            let pick (a, b) = [ if a then 100 else 0, if b then 200 else 0 ]
            """;

    @Test
    void aSumOfChoicesMeetsAsTheSameChoicesAddedDo() {
        assertEquals(shape(read(PLUS, "total")), shape(read(SUM_OF_CHOICES, "total")),
                "the same value written with a total is the same two decisions meeting");
        assertEquals(List.of(List.of(2, 2)), shape(read(SUM_OF_CHOICES, "total")));
    }

    @Test
    void aTotalOverOneChoiceIsNoMeeting() {
        assertEquals(List.of(), read(SUM_OF_ONE, "total"),
                "one decision is consumed alone, so nothing is varied against it");
    }

    @Test
    void anOperationThatTakesNoValueOfTheElementsIsNoMeeting() {
        assertEquals(List.of(), read(LENGTH_OF_CHOICES, "count"),
                "how many elements there are is a function of neither decision");
    }

    @Test
    void aListOnlyBuiltOfChoicesIsNoMeeting() {
        assertEquals(List.of(), read(LIST_OF_CHOICES, "pick"),
                "a list is where two values arrive, not where one is made of them");
    }
}
