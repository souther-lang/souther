package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who may go down the arguments of what an operation answers.
 *
 * <p>Its arguments are numbers of the input and other answers, and an answer is held by every
 * answer made of it however many times it is handed in, so the answers are a graph and the paths
 * down them are two to the depth of a chain of calls each handed the one before it twice. What a
 * reader wants of one is a fact of the positions it is made of ({@code positionsItIsMadeOf}), or
 * is the same of every answer, or is a rebuilding of it ({@code rebuilt}), and each of those is the
 * answer's to give once. A reader that goes down {@code of()} itself pays for every path, and the
 * ones that did took a quarter of a minute at twenty-six calls.
 *
 * <p>The two that still do read one argument of an answer that has one, which a chain of calls
 * each given one thing is a line and not a graph of, so there are no two paths to count.
 */
class OnlyTheAnswerOfAnOperationGoesDownItsOwnArgumentsTest {

    private static final Pattern DECLARED = Pattern.compile(
            "(?<![A-Za-z])WhatAnOperationAnswers\\s+(\\w+)");

    /** A pattern that takes the answer's own components apart. */
    private static final Pattern TAKEN_APART = Pattern.compile(
            "(?<![A-Za-z])WhatAnOperationAnswers\\((var|Stdlib|ValueName)");

    private static final Set<String> OF_ONE_ARGUMENT = Set.of(
            "partition/ConvertedText.java",
            "partition/Pullback.java");

    @Test
    void noReaderOutsideTheOwnerAsksAnAnswerForItsArgumentsButTheOnesOfOneArgument()
            throws IOException {
        Set<String> found = new TreeSet<>();
        Path main = Path.of("src/main/java/souther/compiler");
        try (Stream<Path> sources = Files.walk(main)) {
            for (Path source : (Iterable<Path>) sources
                    .filter(each -> each.toString().endsWith(".java"))::iterator) {
                String relative = main.relativize(source).toString().replace('\\', '/');
                if (relative.equals("meaning/Quantity.java")) {
                    continue;
                }
                String text = Files.readString(source);
                Matcher declared = DECLARED.matcher(text);
                boolean goesDown = TAKEN_APART.matcher(text).find();
                while (declared.find() && !goesDown) {
                    goesDown = Pattern.compile("\\b" + declared.group(1) + "\\.of\\(\\)")
                            .matcher(text).find();
                }
                if (goesDown) {
                    found.add(relative);
                }
            }
        }
        assertEquals(OF_ONE_ARGUMENT, found);
    }
}
