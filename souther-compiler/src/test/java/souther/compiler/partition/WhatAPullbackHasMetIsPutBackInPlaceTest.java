package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a Pullback has met of a container's elements is one object for as long as the place it is
 * held in lasts, and a reading that is not to be taken is put back by rewinding that object.
 *
 * <p>Held by a reading as it was made, a replaced object is not the one the reading goes on to ask
 * of, and a copy taken to be put back is the object afterwards, which the next reading to be put
 * back to it changes. So the field is assigned where a place of its own begins and ends — a
 * comparison's scope and a reading's leaf — and nowhere else.
 */
class WhatAPullbackHasMetIsPutBackInPlaceTest {

    @Test
    void theElementsMetAreAssignedOnlyWhereAPlaceBeginsAndEnds() throws IOException {
        List<String> found = Files.readAllLines(
                        Path.of("src/main/java/souther/compiler/partition/Pullback.java"))
                .stream()
                .map(String::strip)
                .filter(line -> !line.startsWith("*") && !line.startsWith("//")
                        && !line.startsWith("/*"))
                .filter(line -> line.contains("elementsMet = "))
                .toList();

        assertEquals(List.of(
                "private ElementsMet elementsMet = ElementsMet.NONE;",
                "elementsMet = new ElementsMet();",
                "elementsMet = outerElements;",
                "elementsMet = held;",
                "elementsMet = outer;"), found);
    }
}
