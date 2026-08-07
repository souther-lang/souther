package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A document says where its own structure is written, and inside a block whose text is taken as it
 * stands it says the opposite. Remembering only that some block is open is not enough to tell where
 * one ends: a delimiter of another kind would close it, and every blank line and heading in the
 * rest of it would then read as somewhere the document may be cut or a section may begin.
 */
class ABlockTakenAsItStandsIsClosedByWhatOpenedItTest {

    @Test
    void anAsciiDocListingIsNotClosedByALiteralDelimiter() {
        assertEquals(List.of(false, true, true, true, true, true, false),
                opaque("""
                        before
                        ----
                        listing
                        ....
                        still listing
                        ----
                        after"""));
    }

    @Test
    void aMarkdownFenceIsNotClosedByTheOtherFenceCharacter() {
        assertEquals(List.of(false, true, true, true, true, true, false),
                opaque("""
                        before
                        ```
                        fenced
                        ~~~
                        still fenced
                        ```
                        after"""));
    }

    @Test
    void aFenceIsNotClosedByOneShorterThanItself() {
        assertEquals(List.of(true, true, true, true, false),
                opaque("""
                        ````
                        fenced
                        ```
                        ````
                        after"""));
    }

    @Test
    void aLineCarryingAnInfoStringOpensAFenceAndNeverClosesOne() {
        assertEquals(List.of(false, true, true, true, true, false),
                opaque("""
                        before
                        ```java
                        int x = 1;
                        ```java
                        ```
                        after"""));
    }

    @Test
    void aBlockNothingClosesRunsToTheEnd() {
        assertEquals(List.of(false, true, true), opaque("""
                before
                ----
                and on"""));
    }

    private List<Boolean> opaque(String text) {
        boolean[] taken = TakenAsItStands.lines(text.split("\n", -1));
        List<Boolean> said = new java.util.ArrayList<>();
        for (boolean line : taken) {
            said.add(line);
        }
        return said;
    }
}
