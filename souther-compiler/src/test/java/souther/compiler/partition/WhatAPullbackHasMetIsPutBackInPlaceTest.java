package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a Pullback has met of a container's elements is one object for as long as the place it is
 * held in lasts, and a reading that is not to be taken is put back by rewinding that object.
 *
 * <p>Held by a reading as it was made, a replaced object is not the one the reading goes on to ask
 * of, and a copy taken to be put back is the object afterwards, which the next reading to be put
 * back to it changes. So the field is assigned where a place of its own begins and ends — a
 * comparison's scope and a reading's leaf — and nowhere else.
 *
 * <p>What this holds is where the field is assigned, read off the source with the comments taken
 * out and the spacing made one, and it is a check beside what {@code ElementsMet} is held to by
 * its own tests: that a mark is rewound to as often as there are ways from it.
 */
class WhatAPullbackHasMetIsPutBackInPlaceTest {

    private static final Pattern ASSIGNMENT = Pattern.compile(
            "\\belementsMet\\s*=(?!=)\\s*([^;]+);");

    @Test
    void theElementsMetAreAssignedOnlyWhereAPlaceBeginsAndEnds() throws IOException {
        String code = Files.readString(
                        Path.of("src/main/java/souther/compiler/partition/Pullback.java"))
                .replaceAll("(?s)/\\*.*?\\*/", " ")
                .replaceAll("//[^\\n]*", " ");
        List<String> found = new ArrayList<>();
        Matcher each = ASSIGNMENT.matcher(code);
        while (each.find()) {
            found.add(each.group(1).replaceAll("\\s+", " ").strip());
        }

        assertEquals(List.of(
                "ElementsMet.NONE",
                "new ElementsMet()",
                "outerElements",
                "held",
                "outer"), found);
    }
}
