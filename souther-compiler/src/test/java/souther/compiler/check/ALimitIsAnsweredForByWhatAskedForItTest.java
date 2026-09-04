package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.UnreadReason;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A limit this compiler reached while working out a position is answered for by whatever asked for
 * it, and not by everything that named the position.
 *
 * <p>An allowance is held per position and every rule reaching one pays into the machine it finally
 * admits. When one of those machines is refused, what is recorded is a fact about the pattern
 * somebody wrote — and where it is recorded is the position, which is what the spending is arranged
 * by. Which rule asked is not the same question as which rules name the place, and an account that
 * answered the first with the second told an author to go and change a rule that is not why.
 *
 * <p>Two things are lost by asking the position, and both are here. Which rule is answerable is one.
 * Where the reason stands among the parts the author wrote is the other: a limit recovered from a
 * position has no place among them, and a reading that hands its reasons on in the order the author
 * wrote them cannot put it back.
 */
class ALimitIsAnsweredForByWhatAskedForItTest {

    /**
     * One rule whose answer runs past the allowance, beside one rule whose own pattern is larger
     * than any machine this makes. Both are about {@code y}.
     *
     * <p>{@code a{60000}} is written in {@code huge} and nowhere else, so nothing about {@code r} is
     * why that machine was refused.
     */
    private static final String A_LIMIT_ONE_RULE_ASKED_FOR = """
            module demo

            data N = { x: String, y: String }
                invariant r =
                    (String.matches("a{300}", y) && String.matches("b{300}", y))
                    || x == "A"
                invariant huge = String.matches("a{60000}", y)
            """;

    /** The same declaration with the rule that asks for nothing costly taken away. */
    private static final String THE_RULE_THAT_ASKED_FOR_IT_ALONE = """
            module demo

            data N = { x: String, y: String }
                invariant huge = String.matches("a{60000}", y)
            """;

    /**
     * The rule that asked carries the limit, and the rule beside it carries what it was short of on
     * its own.
     *
     * <p>Both halves matter. Naming {@code huge} is right and is not enough: {@code r} standing on
     * a limit its neighbour reached is an author sent to a clause that reads perfectly well.
     */
    @Test
    void aLimitIsCarriedByTheRuleThatAskedForItAndByNothingBeside() {
        Map<String, List<UnreadReason>> standing = standingOn(A_LIMIT_ONE_RULE_ASKED_FOR);

        assertEquals(List.of(UnreadReason.PATTERN_TOO_COSTLY), standing.get("huge at y"),
                "the rule whose pattern was refused answers for it");
        assertEquals(List.of(), standing.getOrDefault("r at y", List.of()),
                "and the rule beside it is answerable for nothing of it: what its own question"
                        + " stands on is the answer at the position, which no rule is answerable"
                        + " for and which is filed nowhere under a rule");
    }

    /**
     * And the position says it all the same.
     *
     * <p>The other half of what this is about, and the half that says which direction the fix runs
     * in. A position is as wide as it is because a machine was refused, and a reader of the place is
     * owed that — what is not owed is an account of a rule built back out of it. Read as "take it
     * off the position", the same test would pass with a reader told a position is exact when it is
     * not.
     */
    @Test
    void andThePositionSaysWhatItWasLeftWith() {
        assertTrue(whatThePositionWasLeftWith(A_LIMIT_ONE_RULE_ASKED_FOR)
                        .contains(UnreadReason.PATTERN_TOO_COSTLY),
                "the place a refused machine widened says so, whoever asked for the machine");
    }

    /**
     * And writing a rule beside another does not change what that other is reported as short of.
     *
     * <p>The invariant, said as the thing an author can watch. What {@code huge} is short of is a
     * fact about {@code huge}, so adding or removing a neighbour that asks for nothing costly leaves
     * it where it was.
     */
    @Test
    void aRuleIsShortOfWhatItIsShortOfWhoeverIsWrittenBesideIt() {
        assertEquals(standingOn(THE_RULE_THAT_ASKED_FOR_IT_ALONE).get("huge at y"),
                standingOn(A_LIMIT_ONE_RULE_ASKED_FOR).get("huge at y"));
    }

    /**
     * What every question of every rule that nothing answered is filed under that rule as, keyed by
     * rule and name.
     *
     * <p>What a rule is answerable for and nothing else. A question may stand on more than this —
     * an answer at its position that was not built is no rule's — and what that comes to is
     * {@code WhatAStandingQuestionIsAccountedForByTest}'s. Here the question is which rule a
     * shortfall was filed under, so what is read is the filing.
     */
    private static Map<String, List<UnreadReason>> standingOn(String source) {
        Map<String, List<UnreadReason>> out = new LinkedHashMap<>();
        read(source).accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted
                            && unaccounted.why()
                            instanceof RuleAccounting.Why.TheValueReadingSays says) {
                        out.put(named(accounting) + " at " + owed, says.why());
                    }
                }));
        return out;
    }

    /** What the position the two rules are both about was left holding, and why. */
    private static List<UnreadReason> whatThePositionWasLeftWith(String source) {
        souther.compiler.values.AdmissibleSet.Completeness said =
                read(source).admits(RuleKey.of("y")).completeness();
        return said instanceof souther.compiler.values.AdmissibleSet.Completeness.Wider wider
                ? wider.why().stream()
                        .filter(souther.compiler.values.AdmissibleSet.Widening.RuleUnread.class
                                ::isInstance)
                        .map(each -> ((souther.compiler.values.AdmissibleSet.Widening.RuleUnread)
                                each).why())
                        .toList()
                : List.of();
    }

    /** The name the author gave the rule, which is how this test says which one it means. */
    private static String named(RuleAccounting accounting) {
        String printed = ((RuleCitation.Named) accounting.cited()).name();
        return printed.substring(printed.indexOf('(') + 1, printed.indexOf(')'));
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(each -> each.diagnostic().code())
                .toList(), "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
