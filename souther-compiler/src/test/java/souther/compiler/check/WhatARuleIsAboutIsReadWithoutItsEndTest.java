package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which number a rule is written about is read from the rule, and not from the end it placed.
 *
 * <p>Nothing here asks what the rules leave the value, where a border goes, or whether anything was
 * narrowed. A rule about the length of a string is about it whether it orders the lengths, names
 * one of them, or holds the value away from one — and a reading that answers the first only for the
 * rules that placed an end is answering with {@link InvariantBound}'s question.
 *
 * <p>That is what left a position whose one rule is {@code String.length(value) /= 0} measured by
 * the string's own order: the length was never a number of the model, so nothing about its floor
 * could come into it.
 */
class WhatARuleIsAboutIsReadWithoutItsEndTest {

    private static final ValueName LENGTH = ValueName.Stdlib.operation("String", "length");

    /** The number an operation answers of the value, as a coordinate names it. */
    private static final NumberAt.OfWhatNumber ITS_LENGTH =
            new NumberAt.OfWhatNumber.OfWhatAnOperationAnswers(LENGTH);

    /** And the value's own. */
    private static final NumberAt.OfWhatNumber ITSELF =
            new NumberAt.OfWhatNumber.OfItsOwnValue();

    @Test
    void anOrderingOfTheLengthIsAboutTheLength() {
        assertEquals(Set.of(ITS_LENGTH), subjectsOf("String", "String.length(value) >= 1"));
    }

    /** The one the issue was written from: it places no end, and it is about the same number. */
    @Test
    void aValueHeldAwayFromTheLengthIsAboutTheLength() {
        assertEquals(Set.of(ITS_LENGTH), subjectsOf("String", "String.length(value) /= 0"));
    }

    /** And so is one that names a length, which places both ends at once and so places neither. */
    @Test
    void aNamedLengthIsAboutTheLength() {
        assertEquals(Set.of(ITS_LENGTH), subjectsOf("String", "String.length(value) == 5"));
    }

    /** Whichever side it was written on, since {@code 1 <= n} says what {@code n >= 1} says. */
    @Test
    void theSideItWasWrittenOnDoesNotComeIntoIt() {
        assertEquals(Set.of(ITS_LENGTH), subjectsOf("String", "1 <= String.length(value)"));
    }

    /**
     * And a rule the arithmetic cannot fold is about the number it names all the same.
     *
     * <p>What the other side holds decides where an end lands. It decides nothing about what the
     * rule is about, so it is not asked here.
     */
    @Test
    void whatItStandsAgainstDoesNotComeIntoItEither() {
        assertEquals(Set.of(ITS_LENGTH),
                subjectsOf("String", "String.length(value) <= 10 * 2"));
    }

    /** A number of the value itself, which is the other of the two a string has. */
    @Test
    void aRuleOnTheValuesOwnOrderIsAboutTheValue() {
        assertEquals(Set.of(ITSELF), subjectsOf("Int", "value /= 0"));
    }

    /** Both, where the model writes about both. Nothing here chooses between them. */
    @Test
    void aModelWritingAboutBothNumbersIsAboutBoth() {
        assertEquals(Set.of(ITS_LENGTH, ITSELF),
                subjectsOf("String", "String.length(value) /= 0", "value >= \"a\""));
    }

    /** A clause naming no number of the value is about none of them. */
    @Test
    void aClauseAboutNoNumberOfTheValueIsAboutNothing() {
        assertEquals(Set.of(), subjectsOf("Int", "1 >= 0"));
    }

    private static Set<NumberAt.OfWhatNumber> subjectsOf(String carrier, String... invariants) {
        StringBuilder source = new StringBuilder("""
                module example.subject

                data Subject = %s
                """.formatted(carrier));
        for (String each : invariants) {
            source.append("    invariant ").append(each).append('\n');
        }
        source.append("""

                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """);
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Type type = sigs.get("take").inputTypes().get(0);
        return DeclaredSubjects.of(type, RuleReadings.of(compilation, module),
                ReadAs.THE_COMPILATION_DOES);
    }
}
