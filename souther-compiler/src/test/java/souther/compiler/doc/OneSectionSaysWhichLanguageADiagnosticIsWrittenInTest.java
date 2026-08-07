package souther.compiler.doc;

import org.junit.jupiter.api.Test;

import java.util.Set;
import java.util.TreeSet;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which language a diagnostic is written in is decided in one place, and the specification states
 * it in one place: the section on compile errors. A second section restating it is a second
 * normative sentence on the same rule, and the two are then kept in step by whoever remembers both.
 *
 * <p>A restatement is not found by searching for the rule's own words. The wording that went stale
 * shared no token with the rule it copied — one said the machine's locale never selects a language,
 * the other said Japanese by default — so what is looked for here is the shape of the claim: a
 * sentence that names a language and is talking about a message. A section may state a requirement
 * that diagnostics are localized; naming the language it lands on is what belongs to one section.
 */
class OneSectionSaysWhichLanguageADiagnosticIsWrittenInTest {

    /** The section that owns the rule. */
    private static final String OWNER = "compile-errors";

    private static final Pattern LANGUAGE = Pattern.compile("\\b(English|Japanese)\\b");
    private static final Pattern ABOUT_A_MESSAGE =
            Pattern.compile("\\b(diagnostics?|messages?|localized)\\b");
    /** A sentence ends at a full stop or a semicolon followed by a space: a specification sentence
     *  states several clauses of one rule, and a semicolon joins them. */
    private static final Pattern SENTENCE_END = Pattern.compile("(?<=[.;])\\s+");

    @Test
    void noSectionOutsideTheOneThatOwnsTheRuleNamesTheLanguageAMessageIsWrittenIn() {
        Set<String> naming = sectionsNamingTheLanguageOfAMessage(SpecDocument.bundled());

        assertEquals(Set.of(OWNER), naming,
                "a section other than `" + OWNER + "` states which language a message is written in");
    }

    /**
     * Without this the assertion above would also hold for a specification that had lost the rule
     * altogether, or for a scan that matched nothing.
     */
    @Test
    void theSectionThatOwnsTheRuleStatesItSoTheScanIsNotMatchingNothing() {
        assertTrue(sectionsNamingTheLanguageOfAMessage(SpecDocument.bundled()).contains(OWNER),
                "the scan found no statement of the rule at all, not even where it is written");
    }

    @Test
    void aLanguageNamedForSomethingOtherThanAMessageIsNotAStatementOfTheRule() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#identifiers]
                == Identifiers

                Keywords are in English, and an identifier written in Japanese binds after
                normalization.

                [#compile-errors]
                == Compile errors

                A message is written in English unless something names another language.
                """);

        assertEquals(Set.of("compile-errors"), sectionsNamingTheLanguageOfAMessage(spec));
    }

    /** The sections with a sentence that both names a language and is talking about a message. */
    private static Set<String> sectionsNamingTheLanguageOfAMessage(SpecDocument spec) {
        Set<String> found = new TreeSet<>();
        for (SpecDocument.Section section : spec.sections()) {
            for (String sentence : SENTENCE_END.split(section.body().replace('\n', ' '))) {
                if (LANGUAGE.matcher(sentence).find() && ABOUT_A_MESSAGE.matcher(sentence).find()) {
                    found.add(section.anchor());
                }
            }
        }
        return found;
    }
}
