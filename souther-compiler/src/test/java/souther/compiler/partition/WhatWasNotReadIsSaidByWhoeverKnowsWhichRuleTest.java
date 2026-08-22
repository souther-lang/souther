package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two authorities answer "this was not read", and which of them it is decides what can be said.
 *
 * <p>A rule was read and could not be used, and the reader that read it knows which rule; or the
 * reading never arrived at the rules of a position, and there is no rule to name because none was
 * observed. Written as one shape with the rule left out where there is none, a consumer would have
 * to read an absent field to know which of the two it was holding — and a report would name a rule
 * for some entries and not the rest with nothing saying why.
 *
 * <p>Both are told under {@code PARTITION_NOT_READ}, and the reason beside each says which limit
 * it is waiting on. {@code PARTITION_RULES_NOT_REACHED} belongs to the finding about a position the
 * axes did measure, which is a different thing to act on and writes the same one field.
 */
class WhatWasNotReadIsSaidByWhoeverKnowsWhichRuleTest {

    /** A rule read and given up on: the position is inside an expression the terms do not name. */
    private static final String A_RULE = """
            module m

            data Ok
            data No

            behavior f : (n: Int) -> Ok | No
            let f (n) = if Int.multiply(n, n) < 10 then Ok else No
            """;

    /**
     * A position whose rules the reading never arrived at.
     *
     * <p>The clause states a relation of every element and is held as a quantifier over the clause
     * it was written in; nothing places one at the position it is about. So there is a rule and no
     * reader that reached it, which is what leaves a position with no rule to name.
     */
    private static final String A_POSITION = """
            module m

            data Ok
            data Item = { charge: Int }
            data Basket = List<Item>
                invariant charged = List.all(i -> i.charge >= 1, value)

            behavior f : (items: Basket) -> Ok
                constructs Ok
            let f (items) = Ok
            """;

    /** A rule finding names the rule, and is told under the word for a rule. */
    @Test
    void aRuleThisReadAndCouldNotUseNamesIt() {
        PartitionEvidence.NotRead said = notRead(A_RULE).getFirst();

        PartitionEvidence.NotRead.ARule rule =
                assertInstanceOf(PartitionEvidence.NotRead.ARule.class, said);
        assertInstanceOf(souther.compiler.check.RuleRef.Comparison.class, rule.rule());
        assertEquals(List.of(Adequacy.Kind.PARTITION_NOT_READ), kinds(A_RULE));
    }

    /**
     * And a position finding names no rule, because nothing observed one.
     *
     * <p>The clause is stated of every element, and what holds it is the quantifier rather than
     * the position — so what stopped this is the reading and not any one clause, and what is said
     * is the position alone. The shape has nowhere to put a rule, which is what stops one being
     * invented.
     */
    @Test
    void aPositionTheReadingDidNotReachNamesNoRule() {
        List<PartitionEvidence.NotRead> said = notRead(A_POSITION);

        assertTrue(said.stream().anyMatch(each ->
                        each instanceof PartitionEvidence.NotRead.APosition
                                && each.reason() == UndividedPosition.Reason.RULES_NOT_READ_AT_ALL),
                said::toString);
        assertFalse(said.stream().anyMatch(each -> each instanceof PartitionEvidence.NotRead.ARule),
                said::toString);
    }

    /**
     * A report names the rule where there is one and the position where there is not, and the two
     * sentences are written apart.
     *
     * <p>One sentence over both would have to say "a rule about it" of an entry with no rule, which
     * is the sentence this is against — an author told that a rule went unread with nothing saying
     * which.
     */
    @Test
    void theTwoAreWrittenApart() {
        assertTrue(human(A_RULE).contains("not read: comparison@"), human(A_RULE));
        assertFalse(human(A_RULE).contains("not read: n "), human(A_RULE));
        assertTrue(human(A_POSITION).contains("not read: items[*].charge ("), human(A_POSITION));
    }

    private static List<Adequacy.Kind> kinds(String model) {
        return findings(model).stream()
                .filter(each -> each.kind() == Adequacy.Kind.PARTITION_NOT_READ
                        || each.kind() == Adequacy.Kind.PARTITION_RULES_NOT_REACHED)
                .map(Adequacy.Finding::kind).toList();
    }

    private static List<Adequacy.Finding> findings(String model) {
        return report(model).modules().get(0).behaviors().get(0).findings();
    }

    private static List<PartitionEvidence.NotRead> notRead(String model) {
        return report(model).modules().get(0).behaviors().get(0).partition().notRead();
    }

    private static String human(String model) {
        return report(model).human(SourceNameResolver.identity());
    }

    private static AdequacyReport report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation);
    }
}
