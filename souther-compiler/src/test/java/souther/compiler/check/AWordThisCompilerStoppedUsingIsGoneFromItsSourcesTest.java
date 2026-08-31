package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A word this compiler stopped using is gone from what it is written in.
 *
 * <p>Held over the text and not over the classes, because what survives a rename is the prose. A
 * {@code {@link}} to a member that no longer exists compiles, and so does a paragraph explaining a
 * mechanism that was taken out — so the reader of the file learns a vocabulary the compiler no
 * longer has, and the next thing written there is written in it.
 *
 * <p>The list is names that were removed because they said one thing for two, in settling what a
 * rule of a value calls a place apart from where a row writes one. It is not a rule against words
 * in general: a name is here because it was deleted, and it comes off this list only by coming
 * back.
 */
class AWordThisCompilerStoppedUsingIsGoneFromItsSourcesTest {

    /** Read once: what this asks of it does not change between its checks. */
    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /**
     * What was taken out.
     *
     * <p>Names, and never a way of writing one: no parentheses on a method, because the place a
     * name most outlives its member is a {@code {@link}}, which has none. A name is written with an
     * owner here only where the name alone still names something this compiler has — {@code
     * THE_VALUE} is {@code RuleKey}'s now — and then it is the owner that says which is meant.
     */
    private static final List<String> GONE = List.of(
            "PositionReading",
            "positionsUnder",
            "atOwnPath",
            "fieldKeyUnder",
            "fieldKey",
            "stepsSpelledUnder",
            "stepsSpelled",
            "FieldDomains.THE_VALUE");

    @Test
    void nothingIsWrittenInAVocabularyThisCompilerGaveUp() throws IOException {
        List<Pattern> gone = GONE.stream().map(AWordThisCompilerStoppedUsingIsGoneFromItsSourcesTest::asAWord)
                .toList();
        List<String> found = new ArrayList<>();
        for (Path source : REPOSITORY.mainJavaSources()) {
            String written = Files.readString(source, StandardCharsets.UTF_8);
            for (int at = 0; at < gone.size(); at++) {
                if (gone.get(at).matcher(written).find()) {
                    found.add(source.getFileName() + " still says `" + GONE.get(at) + "`");
                }
            }
        }

        assertEquals(List.of(), found,
                "these say what a rule calls a place and where a row writes one in one word, and"
                        + " the word was taken out");
    }

    /**
     * Every one of them is found where javac does not look, which is what this is for.
     *
     * <p>The scan above passes on a list that finds nothing, and a name written so that it only
     * matches a call finds nothing in a link — the one place a reference outlives the member it
     * refers to. So each name is read back in the way a link writes it.
     */
    @Test
    void eachOfThemIsCaughtWhereAJavadocLinkWouldPutIt() {
        List<String> missed = new ArrayList<>();
        for (String name : GONE) {
            String linked = name.contains(".") ? name.replace('.', '#') : "SomeType#" + name;
            if (!asAWord(name).matcher("{@link " + linked + "} explains it").find()) {
                missed.add(name + " is not found in `{@link " + linked + "}`");
            }
        }

        assertEquals(List.of(), missed,
                "a name is on this list because it was removed, and a link to a removed member is"
                        + " what nothing else refuses");
    }

    /**
     * The word where it is the whole name and not where it is part of one.
     *
     * <p>{@code PositionReadingBlocked} is a type this compiler still has, and a scan for the text
     * of a removed name finds it inside that one — the same mistake the removed names were: a
     * spelling standing in for the thing. So what is matched is the name with no identifier
     * character on either side of it.
     *
     * <p>An owner reaches its member by a dot in a sentence and by a {@code #} in a link, and both
     * are the same name, so either separator matches.
     */
    private static Pattern asAWord(String name) {
        String written = Pattern.quote(name).replace(".", "\\E[.#]\\Q");
        return Pattern.compile("(?<![A-Za-z0-9_])" + written + "(?![A-Za-z0-9_])");
    }
}
