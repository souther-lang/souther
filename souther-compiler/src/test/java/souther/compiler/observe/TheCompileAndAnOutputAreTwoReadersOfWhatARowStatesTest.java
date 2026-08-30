package souther.compiler.observe;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a row states is a value, and the two things that read one are not written in terms of each
 * other.
 *
 * <p>Three packages and one direction. {@code observe} is what a value stated by a text and a value
 * a run answered are said in; {@code examples} is this compiler reading a text and running what it
 * names; {@code program} is what an output outside this compiler is handed. The second and the
 * third are two readers of the first, and neither is above the other: a compile that read the
 * snapshot's vocabulary would be checking a model against what it is about to publish, and a
 * snapshot that named the compile's would carry the reading into what it publishes.
 *
 * <p>Read off the class files, because that is what the rule is about. An {@code import} is not a
 * dependency — it is gone by the time javac is done — and a type argument is not in a descriptor, so
 * a check reading either alone would pass a {@code List<FixtureReader>} without seeing it. What
 * {@link WhatWasCompiled#typesNamedBy} answers is every type a class names, wherever it named it.
 */
class TheCompileAndAnOutputAreTwoReadersOfWhatARowStatesTest {

    private static final String OBSERVE = "souther.compiler.observe";
    private static final String EXAMPLES = "souther.compiler.examples";
    private static final String PROGRAM = "souther.compiler.program";

    /** What a value is said in names neither of its readers. */
    @Test
    void whatAValueIsSaidInNamesNeitherOfItsReaders() {
        assertEquals(List.of(), namedFrom(OBSERVE, EXAMPLES),
                "the vocabulary a row states its values in named the compile that reads a text");
        assertEquals(List.of(), namedFrom(OBSERVE, PROGRAM),
                "the vocabulary a row states its values in named what an output is handed");
    }

    /**
     * And the two readers do not name each other.
     *
     * <p>Either direction is the same defect. The compile reading the snapshot would hold a model to
     * what it is about to publish of it; the snapshot naming the compile would carry a reading of a
     * text into an artifact that exists so nothing has to read one.
     */
    @Test
    void andNeitherReaderNamesTheOther() {
        assertEquals(List.of(), namedFrom(PROGRAM, EXAMPLES),
                "what an output is handed named the compile that read the text");
        assertEquals(List.of(), namedFrom(EXAMPLES, PROGRAM),
                "the compile that reads a text named what an output is handed");
    }

    /**
     * And both read what a value is said in, so the checks above saw something.
     *
     * <p>A walk that reached nothing answers the same as one that reached everything and found
     * nothing wrong with it.
     */
    @Test
    void andBothReadWhatAValueIsSaidIn() {
        assertFalse(namedFrom(EXAMPLES, OBSERVE).isEmpty(),
                "the compile names nothing a value is said in, so the walk found no classes");
        assertFalse(namedFrom(PROGRAM, OBSERVE).isEmpty(),
                "what an output is handed names nothing a value is said in");
    }

    /** Every class of {@code from} that names a type of {@code named}, and which type it named. */
    private static List<String> namedFrom(String from, String named) {
        List<String> found = new ArrayList<>();
        for (String each : WhatWasCompiled.classes()) {
            if (!packageOf(each).equals(from)) {
                continue;
            }
            for (String type : WhatWasCompiled.typesNamedBy(each)) {
                if (packageOf(type).equals(named)) {
                    found.add(each + " -> " + type);
                }
            }
        }
        return found;
    }

    /** The package a binary name is in. A nested class is in its outer one's, which is what {@code $}
     *  says and {@code .} does not. */
    private static String packageOf(String binaryName) {
        int at = binaryName.lastIndexOf('.');
        return at < 0 ? "" : binaryName.substring(0, at);
    }
}
