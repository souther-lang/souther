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
    /** What the claim is about, which is a thing and not what is done to it: `localized` is a
     *  predicate a manual takes as readily as a diagnostic does, and reading it as the subject
     *  would make a localized document a statement about a diagnostic. Either word opens a
     *  sentence as readily as it sits inside one, and a claim is the same claim either way. */
    private static final Pattern ABOUT_A_MESSAGE =
            Pattern.compile("\\b(diagnostics?|messages?)\\b", Pattern.CASE_INSENSITIVE);
    /** A sentence ends at a full stop followed by a space. A semicolon is not an end: a
     *  specification sentence states the clauses of one rule and a semicolon joins them, so
     *  ending there would read one claim as two and find a language in one half and a message in
     *  the other. */
    private static final Pattern SENTENCE_END = Pattern.compile("(?<=\\.)\\s+");

    @Test
    void noSectionOutsideTheOneThatOwnsTheRuleNamesTheLanguageAMessageIsWrittenIn() {
        Set<String> elsewhere = new TreeSet<>(sectionsNamingTheLanguageOfAMessage(SpecDocument.bundled()));
        elsewhere.remove(OWNER);

        assertEquals(Set.of(), elsewhere,
                "these state which language a message is written in, and `" + OWNER + "` owns that");
    }

    /** The other half of the rule: it is stated, and stated where it is owned. */
    @Test
    void theSectionThatOwnsTheRuleIsWhereItIsStated() {
        assertTrue(sectionsNamingTheLanguageOfAMessage(SpecDocument.bundled()).contains(OWNER),
                "`" + OWNER + "` no longer says which language a message is written in");
    }

    @Test
    void aLanguageNamedForSomethingOtherThanAMessageIsNotAStatementOfTheRule() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#identifiers]
                == Identifiers

                Keywords are in English, and an identifier written in Japanese binds after
                normalization.

                [#documents]
                == Documents

                The reference manual is localized in Japanese.

                [#compile-errors]
                == Compile errors

                A message is written in English unless something names another language.
                """);

        assertEquals(Set.of("compile-errors"), sectionsNamingTheLanguageOfAMessage(spec));
    }

    /**
     * The claim is one claim however its clauses are punctuated. A semicolon joins the clauses of
     * one rule rather than ending it, so reading it as an end would look for a language and a
     * message on either side of it and find one on each — which is the restatement this looks for,
     * written in two clauses.
     */
    @Test
    void aRestatementWrittenInTwoClausesIsStillOneStatementOfTheRule() {
        SpecDocument spec = SpecDocument.of("""
                = A specification

                [#non-functional]
                == Non-functional requirements

                Diagnostics are localized; Japanese is the default.

                [#compile-errors]
                == Compile errors

                A message is written in English unless something names another language.
                """);

        assertEquals(Set.of("compile-errors", "non-functional"), sectionsNamingTheLanguageOfAMessage(spec));
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
