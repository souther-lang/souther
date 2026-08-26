package souther.compiler.stdlib;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.Parameter;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the library is asked about an operation, it is asked with the operation.
 *
 * <p>{@code souther.list} declares {@code foldFrom} and the library publishes it as
 * {@code List.foldFrom}. Which part of that spelling is the alias is the library's own to say, so a
 * reader that renders an operation to look it up is asking the library to resolve a name it had
 * just been handed — right for exactly as long as the rendering and the identity agree.
 *
 * <p>Every accessor taking the operation is what stops that, and it holds only while the tables
 * behind them are keyed by the operation too: an accessor that narrows its parameter and renders it
 * inside has moved the join rather than removed it. What keeps both true is that the operation is
 * what {@code Builder.declares} files under, so a spelling has nowhere to become a key.
 *
 * <p>Written as the list of methods that may take a written name, because a list is what makes a
 * new one a decision. A question genuinely about a spelling belongs here with its reason; a
 * question about an operation does not.
 */
class TheLibraryIsAskedWithTheOperationAndNotASpellingTest {

    /**
     * The questions a written name is the subject of, and why each of them is.
     *
     * <p>One turns a spelling into the operation it reaches, which is the way in for a reader that
     * has only a spelling and the only place the two meet. One names a module. Two answer what a
     * reader might have meant by a bare word, which is a question about words.
     */
    private static final Map<String, String> ABOUT_A_SPELLING = Map.of(
            "operation", "turns a written name into the operation it reaches",
            "languageDeclarationsIn", "names a library module",
            "qualifiedCandidates", "what a bare word could have meant",
            "candidateList", "and the same, written out for a reader");

    @Test
    void nothingElseTheLibraryAnswersIsAskedWithAWrittenName() {
        List<String> asked = new ArrayList<>();
        for (Method method : Stdlib.class.getDeclaredMethods()) {
            if (!java.lang.reflect.Modifier.isPublic(method.getModifiers())) {
                continue;
            }
            for (Parameter parameter : method.getParameters()) {
                if (parameter.getType() == String.class
                        && !ABOUT_A_SPELLING.containsKey(method.getName())) {
                    asked.add(method.getName());
                }
            }
        }

        assertEquals(List.of(), asked.stream().sorted().distinct().toList(),
                "this takes a written name. Take the operation instead, or say above what makes it"
                        + " a question about the spelling");
    }

    /** The control: the four are still there, so an empty answer above is an answer and not a
     *  reading of the wrong class. */
    @Test
    void andTheOnesThatAreAboutASpellingAreStillAsked() {
        List<String> found = new ArrayList<>();
        for (Method method : Stdlib.class.getDeclaredMethods()) {
            if (ABOUT_A_SPELLING.containsKey(method.getName())) {
                found.add(method.getName());
            }
        }

        assertTrue(found.containsAll(ABOUT_A_SPELLING.keySet()),
                () -> "named above and not declared: " + found);
    }
}
