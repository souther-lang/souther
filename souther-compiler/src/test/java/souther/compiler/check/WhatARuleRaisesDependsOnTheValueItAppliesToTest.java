package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.check.RuleReadings;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a rule raises is what it raises at one value, and how much of it there is is the model's
 * shape.
 *
 * <p>{@code Price} is bounded by a clause of its own. A record with a {@code was} and a {@code now}
 * of that type is held to that clause at both places, so it raises there twice what it raises at
 * {@code Price} itself; a record with one field of the type raises it once. None of those is a
 * repetition of another — a row whose {@code was} satisfies the rule says nothing about its
 * {@code now} — and none of them is a reading happening more than once.
 *
 * <p><b>Which is what {@link Required} says now and did not before.</b> It was described as what
 * one rule of the model raises, full stop. Measuring the corpora is what refused that: the same
 * clause reaching several values raises questions none of them spells the same way, since
 * {@link Owed} is over a {@link RuleKey} and a key is relative to the value being read — and raises
 * a different number of them wherever a value carries the type twice.
 *
 * <p>Held here so the sentence has something under it. A cardinality written only in a comment is
 * one the next change can make false without anything saying so.
 */
class WhatARuleRaisesDependsOnTheValueItAppliesToTest {

    /** One bounded type, and two records holding it a different number of times. */
    private static final String SOURCE = """
            module example.held

            data Price = Int
                invariant positive = value >= 1

            data Pair = { was: Price, now: Price }

            data One = { only: Price }

            data Taken

            behavior take : (p: Pair) -> Taken
            """;

    @Test
    void aValueHoldingTheTypeTwiceRaisesTheQuestionsTwice() {
        assertEquals(2 * raisedBy("One").obligations().size(),
                raisedBy("Pair").obligations().size(),
                "`Pair` is held to the clause at both of its fields and `One` at its one");
    }

    @Test
    void andNeitherIsWhatItRaisesAtTheValueItIsDeclaredOn() {
        assertEquals(raisedBy("Price").obligations().size(),
                raisedBy("One").obligations().size(),
                "one place either way, so the same questions are raised");
        assertNotEquals(raisedBy("Price"), raisedBy("One"),
                "and they are not the same questions: each names its own place");
    }

    /** The questions are about the places the holding value calls its own. */
    @Test
    void theQuestionsAreAskedInTheHoldingValuesWords() {
        assertEquals(Set.of("was", "now"), placesIn(raisedBy("Pair")),
                "`Pair` is held to it at the two names it wrote");
        assertEquals(Set.of("only"), placesIn(raisedBy("One")),
                "and `One` at the one it wrote");
    }

    /** What the clause of {@code Price} raises at {@code type}. */
    private static Required raisedBy(String type) {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, type));
        assertNotNull(symbols.declaredNode(named.key()), "no `" + type + "` declared");
        java.util.Collection<Required> raised = FieldDomains
                .of(named, RuleReadings.of(compilation, module),
                        ReadAs.THE_COMPILATION_DOES).required().values();
        assertEquals(1, raised.size(), type + " is held to one rule here");
        return raised.iterator().next();
    }

    /** What the questions are about, as the value raising them spells it. */
    private static Set<String> placesIn(Required raised) {
        return raised.obligations().stream()
                .map(each -> switch (each) {
                    case Owed.AdmittedValues it -> it.path().toString();
                    case Owed.Boundary it -> it.on().position().toString();
                })
                .collect(java.util.stream.Collectors.toUnmodifiableSet());
    }
}
