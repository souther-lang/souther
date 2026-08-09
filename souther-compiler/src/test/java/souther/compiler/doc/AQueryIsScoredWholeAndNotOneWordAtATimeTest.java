package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.io.ByteArrayOutputStream;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.util.Comparator;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A query nobody's name and nobody's prose says whole is answered by its words, and the answer is
 * the query's, not its first word's. Ranking each word on its own and laying the results end to end
 * spends the whole answer on whichever word came first: a section that says four of the words is
 * held behind every section that says the opening one, and the reader is answered for a query they
 * did not write.
 *
 * <p>The word a section says is a word, too. A run of characters that happens to sit inside another
 * word is not the document saying it — {@code an} is not what {@code command} says — and a fallback
 * that counts those has its commonest words matching everywhere and deciding everything.
 */
class AQueryIsScoredWholeAndNotOneWordAtATimeTest {

    private final SpecDocument fixture = SpecDocument.of("""
            = A Specification

            [#all]
            == Everything

            nested if else belongs, all of them written here.

            [#some]
            == Two of them

            else and belongs, written down.

            [#one]
            == Only the opening one

            nested, and nothing more.
            """);

    private final SpecDocument words = SpecDocument.of("""
            = A Specification

            [#whole]
            == A whole word

            an else.

            [#run]
            == A run of characters

            command and demand.
            """);

    private String search(String term) {
        ByteArrayOutputStream out = new ByteArrayOutputStream();
        PrintStream print = new PrintStream(out, true, StandardCharsets.UTF_8);
        DocCommand.run(new String[]{"--search", term, "--limit", "0"}, print,
                new PrintStream(ByteArrayOutputStream.nullOutputStream(), true, StandardCharsets.UTF_8));
        return out.toString(StandardCharsets.UTF_8);
    }

    @Test
    void theSectionThatSaysMoreOfTheQueryComesFirst() {
        List<SpecDocument.Hit> hits = fixture.rank(DocName.words("nested if else belongs"), Match.WORD);

        assertEquals(List.of("all", "some", "one"),
                hits.stream().map(h -> h.section().anchor()).toList(),
                "four of the words outranks two, and two outranks the one the query opens with");
    }

    @Test
    void aHitSaysHowManyOfTheQuerysWordsItHolds() {
        List<SpecDocument.Hit> hits = fixture.rank(DocName.words("nested if else belongs"), Match.WORD);

        assertEquals(List.of(4, 2, 1), hits.stream().map(SpecDocument.Hit::matched).toList());
    }

    @Test
    void aWordIsAWholeWordAndNotARunOfCharactersInsideAnother() {
        List<SpecDocument.Hit> hits = words.rank(DocName.words("an else"), Match.WORD);

        assertEquals(List.of("whole"), hits.stream().map(h -> h.section().anchor()).toList(),
                "`command` and `demand` are not the document saying `an`");
    }

    @Test
    void aRepeatedWordIsNotWorthTwiceAsMuch() {
        List<SpecDocument.Hit> once = fixture.rank(DocName.words("nested if else belongs"), Match.WORD);
        List<SpecDocument.Hit> twice = fixture.rank(
                DocName.words("nested if else belongs if else"), Match.WORD);

        assertEquals(once.stream().map(h -> h.section().anchor()).toList(),
                twice.stream().map(h -> h.section().anchor()).toList(),
                "a query that says a word twice asks for the same thing");
    }

    @Test
    void theOrderTheWordsWereTypedInDoesNotDecideTheAnswer() {
        assertEquals(search("string literal escape backslash"),
                search("backslash escape literal string"),
                "the same words asked for in another order are the same question");
    }

    @Test
    void andThatHoldsOfTheSpecificationItselfAndNotOnlyOfAFixture() {
        SpecDocument spec = SpecDocument.bundled();
        List<String> asked = DocName.words("nested if else which if an else belongs to");

        List<SpecDocument.Hit> hits = spec.rank(asked, Match.WORD);

        assertEquals(hits, hits.stream()
                        .sorted(Comparator.comparingInt(SpecDocument.Hit::matched).reversed())
                        .toList(),
                "no section that says more of the query sits below one that says less of it");
        assertTrue(hits.getFirst().matched() > 1,
                "and the answer is not the opening word's: " + hits.getFirst().section().anchor()
                        + " says " + hits.getFirst().matched() + " of them");
    }
}
