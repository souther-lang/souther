package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a comparison that drew no line is reported as, read off what the comparison is.
 *
 * <p>A table, because the answers are only reviewable together. Each row is one shape of rule, and
 * what tells the rows apart is what the author wrote — not which of this compiler's readers happened
 * to answer first. Written the other way round, the word a report printed came from the arithmetic
 * declining to answer, so two rules of one kind were described as two kinds and two kinds as one.
 *
 * <p>The rows that draw a line are here as well as the rows that do not. A rule the arithmetic reads
 * still says what it could not divide, and pinning only the rules that stop would let one of these
 * quietly become the other.
 */
class WhatStoppedAComparisonIsReadOffWhatItIsTest {

    /**
     * The language's own arithmetic over two positions, read as the relation of the two it is and
     * not as a value made of them. What the other reaches is asked of it as of any relation: at
     * the least {@code Int}, {@code a} needs a {@code b} past the greatest. A difference is about
     * how far apart the two are, which moving both together leaves as it was, so it divides
     * neither.
     */
    @Test
    void arithmeticOverTwoPositionsRelatesThem() {
        assertEquals(List.of(UndividedPosition.Reason.RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE),
                whyAt(guard("a: Int, b: Int", "Int.add(a, b) > 10"), "a"));
        assertEquals(List.of(UndividedPosition.Reason.RULE_RELATING_TWO_VALUES),
                whyAt(guard("a: Int, b: Int", "Int.subtract(b, a) > 10"), "b"));
    }

    /**
     * The same arithmetic outside the fragment it is read in. The form was seen and not taken
     * apart, which is a wider reading of forms and not a statement about any operation: the language
     * has an operator for a product, so an author is not being asked to invert anything.
     */
    @Test
    void arithmeticOutsideTheFragmentIsAFormNobodyReads() {
        assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                whyAt(guard("a: Int", "Int.multiply(a, a) > 10"), "a"));
    }

    /**
     * An operation answered the value the rule is about, and the arithmetic met it where it stopped:
     * a remainder by a value a row writes has no period, so there is no remainder for a line on the
     * values to be drawn at. Said of the divisor, which is what an author would change.
     *
     * <p>Told only that a value was made from the position, an author goes looking for a statement
     * about an operation that is not there to be written.
     */
    @Test
    void aRemainderByAValueARowWritesIsNamedForItsDivisor() {
        PartitionEvidence measured = guard("a: Int, b: Int", "Int.floorMod(a, b) > 10");

        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(measured, "a"));
        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(measured, "b"));
    }

    /**
     * An operation the library writes in this language is one of those all the same.
     *
     * <p>{@code Int.abs} has a body, and that body is not what the reading of rules looks at. The
     * tree such a reading is made over keeps the operation standing, so what the author wrote —
     * a comparison against what an operation answered — is what is there to be read, through what
     * the library states of the operation, as every other operation is.
     *
     * <p><b>Which is a decision about who owns a partition's contributions, taken here.</b> The
     * comparisons inside {@code Int.abs} are that operation's implementation, and a caller does not
     * owe rows for them: a line at nought came out of the body forking there, and the model that
     * called it never said anything about nought. So the caller's rule is read for what the caller
     * wrote, and what {@code abs} does to the values is a fact about the operation — the cases the
     * library states of it, proved of its body — and with it the rule is read to the end and
     * nothing stopped it.
     */
    @Test
    void anOperationWrittenInThisLanguageIsAnOperationLikeAnyOther() {
        assertEquals(List.of(), whyAt(guard("a: Int", "Int.abs(a) > 10"), "a"));
    }

    /**
     * Which argument an operation was given is part of what the rule is, so both positions are
     * named however the author ordered them.
     */
    @Test
    void bothArgumentsOfAnOperationAreNamed() {
        PartitionEvidence measured =
                guard("a: Int, b: Int", "Int.floorMod(b, a) > 10");

        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(measured, "a"));
        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(measured, "b"));
    }

    /**
     * An operation this reads perfectly well, beside a form it does not. What is missing is the
     * form, and the operation is not what an author would change.
     *
     * <p>Read off the sides, the answer was about the length: whichever side held an operation was
     * the one blamed, so an operation became more likely to be named for its neighbour the more of
     * them this learned to read.
     *
     * <p>Filed at the length, which is the number the reading was after when it stopped. The rule
     * bounds the length and says nothing about which strings may stand there, so the string's own
     * values are not what went unread.
     */
    @Test
    void anOperationThisReadsIsNotBlamedForTheFormBesideIt() {
        PartitionEvidence measured = guard("s: String",
                "String.length(s) > Int.multiply(String.length(s), String.length(s))");

        assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                whyAt(measured, "String.length(s)"));
        assertEquals(List.of(), whyAt(measured, "s"),
                "the string's own values are not what the rule is about");
    }

    /**
     * And the operation is named where it is what stopped the reading, over the same position and
     * the same shape of comparison. The pair is the whole of the argument: one word for both would
     * be a rule about which side an operation was written on.
     */
    @Test
    void anOperationThisDoesNotReadIsNamed() {
        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(guard("a: Int", "Int.floorMod(a, a) > 10"), "a"));
    }

    /**
     * A rule read from end to end whose quantity the position does not appear in. Nothing fell
     * short here: there was no line in it to draw.
     *
     * <p>Told apart from a reading that stopped, which used to be the same absence. Answered as a
     * form nobody could read, it sent an author to rewrite a spelling this compiler had read
     * completely.
     */
    @Test
    void aRuleReadToTheEndThatCutsNothingSaysThat() {
        assertEquals(List.of(UndividedPosition.Reason.RULE_CUTS_NOTHING),
                whyAt(guard("a: Int", "Int.subtract(a, a) > 0"), "a"));
    }

    /**
     * What the rule cuts is what it is about, and how it was spelled does not overrule that.
     *
     * <p>{@code a - a > b - b} names a position on each side and cuts nothing at all. Asked of the
     * sides first, one position on each was enough to call it a relation between two of them — a
     * class about two positions this compiler is waiting to be able to state, for a rule that
     * states nothing about either. The single-position cancellation beside it does not catch this:
     * there is only one position there for the sides to find.
     */
    @Test
    void whatARuleCutsOverrulesWhatItsSidesMention() {
        assertEquals(List.of(UndividedPosition.Reason.RULE_CUTS_NOTHING),
                whyAt(guard("a: Int, b: Int",
                        "Int.subtract(a, a) > Int.subtract(b, b)"), "a"));
    }

    /**
     * A helper is a binding round the expression it became, and what the expression is made of is
     * its body. An argument the body never reads is no part of the value.
     *
     * <p>Read as both, {@code ignored(a, b)} was an expression about {@code a}: the rule came back
     * as one relating two positions, and a reader was sent to a position the value does not depend
     * on. What reaches an argument is the body reading its name, which is the same way the
     * arithmetic beside this reaches one.
     */
    @Test
    void anArgumentAHelperDoesNotReadIsNoPartOfWhatItAnswers() {
        String model = """
                module demo

                data Ok
                data No

                let second (x: Int, y: Int): Int = Int.multiply(y, y)

                behavior f : (a: Int, b: Int) -> Ok | No
                let f (a, b) = {
                    guard second(a, b) > 10 else No
                    Ok
                }
                """;

        assertEquals(List.of(), whyAt(measured(model), "a"));
        assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                whyAt(measured(model), "b"));
    }

    /** And a name over an expression answers what the expression answers. */
    @Test
    void namingAnExpressionDoesNotChangeWhatItIsMadeOf() {
        String named = """
                module demo

                data Ok
                data No

                let squared (x: Int): Int = Int.multiply(x, x)

                behavior f : (a: Int) -> Ok | No
                let f (a) = {
                    guard squared(a) > 10 else No
                    Ok
                }
                """;

        assertEquals(whyAt(guard("a: Int", "Int.multiply(a, a) > 10"), "a"),
                whyAt(measured(named), "a"));
    }

    /**
     * An operation with arithmetic written round it is still the operation that stopped the
     * reading, and a clause of the same shape says the same thing.
     *
     * <p>The two readers name different things: a body names a position of an input, and a clause
     * names a coordinate of the value it is written about, of which an operation's answer is not
     * one. Read as an atom and found unprojectable afterwards, the clause reader had thrown the
     * operation away and answered from the shape of the whole side — so one token of arithmetic
     * outside the call was the difference between two sentences for one rule.
     */
    @Test
    void arithmeticRoundAnOperationDoesNotChangeWhatStoppedTheReading() {
        for (String condition : List.of("Int.floorMod(a, b) <= 30",
                "Int.add(Int.floorMod(a, b), 1) <= 30",
                "Int.add(1, Int.floorMod(a, b)) <= 30")) {
            assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                    whyAt(guard("a: Int, b: Int", condition), "a"), condition);
        }
    }

    /**
     * A value bound in the body whose arithmetic stopped is that stop wherever it is compared. An
     * operation whose answer is one of several values — the greater, the lesser, the value or its
     * negation — turns the comparison into a relation for each, and the relation over the bound
     * value draws no line for the reason the value does not: what a reader is sent to is the
     * product, the divisor, or the operation that made the value, as with the comparison written
     * without the operation round it.
     */
    @Test
    void aValueWhoseArithmeticStoppedIsThatStopUnderAnOperationAnsweringOneOfSeveral() {
        String parameters = "a: Int, b: Int, c: Int";
        for (String bound : List.of("let p = a * b", "let p = Int.floorMod(a, b)")) {
            List<UndividedPosition.Reason> alone = whyAt(guard(parameters, bound, "p <= c"), "a");
            assertEquals(1, alone.size(), bound);
            for (String condition : List.of("Int.max(0, p) <= c", "Int.min(0, p) <= c",
                    "Int.abs(p) <= c")) {
                PartitionEvidence measured = guard(parameters, bound, condition);
                for (String position : List.of("a", "b", "c")) {
                    assertEquals(alone, whyAt(measured, position),
                            bound + " | " + condition + " at " + position);
                }
            }
        }
        assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                whyAt(guard(parameters, "let p = a * b", "p <= c"), "a"));
        assertEquals(List.of(UndividedPosition.Reason.NON_CONSTANT_REMAINDER_DIVISOR),
                whyAt(guard(parameters, "let p = Int.floorMod(a, b)", "p <= c"), "a"));
        // Written inline, the product is the same number with no name over it.
        assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                whyAt(guard(parameters, "Int.max(0, a * b) <= c"), "a"));
    }

    /**
     * And where the bound value was made by an operation the arithmetic takes no form of, each
     * place words it as it does for the comparison without the operation round it.
     */
    @Test
    void aValueAnOperationMadeIsWordedAtEachPlaceUnderAnOperationAnsweringOneOfSeveral() {
        String parameters = "s: String, c: Int";
        String bound = "let k = String.length(String.trim(s))";
        PartitionEvidence alone = guard(parameters, bound, "k - c < 2");
        PartitionEvidence under = guard(parameters, bound, "Int.abs(k - c) < 2");

        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(alone, "s"));
        for (String position : List.of("s", "c")) {
            assertEquals(whyAt(alone, position), whyAt(under, position), position);
        }
    }

    /**
     * Two values whose readings stopped at two different operations are no one operation, and the
     * relations they leave undrawn are named for neither: naming the first would say of the second
     * that it was not there. Which of them is written first does not choose.
     */
    @Test
    void twoValuesStoppedAtDifferentOperationsAreNamedForNeither() {
        String parameters = "a: Int, b: Int, c: Int";
        String bound = "let p = a * b\n    let q = Int.floorMod(a, b)";
        for (String condition : List.of("Int.max(p, q) <= c", "Int.max(q, p) <= c")) {
            assertEquals(List.of(UndividedPosition.Reason.RULE_MEANING_NOT_READ),
                    whyAt(guard(parameters, bound, condition), "a"), condition);
        }
    }

    /**
     * A relation that drew no line for nothing that stopped is several lines read to the end, and
     * a product beside it does not name the rule. How many elements meet something, held against a
     * value found in the list, is no line and stopped at nothing; naming the product would say of
     * that relation that it was not there, and an author who took the product away would still
     * have no line.
     */
    @Test
    void aRelationReadToTheEndIsNotNamedForTheProductBesideIt() {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (a: Int, b: Int, c: Int, xs: List<Int>) -> Ok | No
                let f (a, b, c, xs) = {
                    let m = List.length(List.filter(x -> x > 0, xs))
                    let k = Option.withDefault(0, List.find(x -> x > a, xs))
                    %s
                    guard %s else No
                    Ok
                }
                """;
        PartitionEvidence alone = measured(model.formatted("", "Int.max(0, m - k) <= c"));
        PartitionEvidence beside = measured(model.formatted("let p = a * b",
                "Int.max(p, m - k) <= c"));

        assertEquals(List.of(UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE),
                whyAt(alone, "c"));
        for (String position : List.of("a", "b", "c")) {
            assertEquals(List.of(UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE),
                    whyAt(beside, position).stream()
                            .filter(why -> why != UndividedPosition.Reason.RULE_RELATING_TWO_VALUES)
                            .toList(), position);
        }
    }

    /**
     * A relation of the input's values to another value is that among several relations as it is
     * alone, and leaves the lines beside it to be drawn: the product beside it is what keeps them
     * from being drawn, and is named. A count of the different values a list holds is about how
     * its values stand to one another, and a value found in the list is no position's; each is
     * such a relation, and the two say the same.
     */
    @Test
    void aRelationToAnotherValueBesideAProductLeavesTheProductNamed() {
        String parameters = "a: Int, b: Int, c: Int, xs: List<Int>";
        for (String bound : List.of("let n = List.length(List.distinct(xs))",
                "let n = Option.withDefault(0, List.find(x -> x > a, xs))")) {
            assertEquals(List.of(UndividedPosition.Reason.NON_AFFINE_PRODUCT),
                    whyAt(guard(parameters, "let p = a * b\n    " + bound,
                            "Int.max(p, n) <= c"), "c"), bound);
        }
    }

    /**
     * A bound value whose arithmetic did not stop is read through its name: a name over a sum
     * under {@code Int.max} is read as the sum written there is.
     */
    @Test
    void aValueWhoseArithmeticWasReadIsReadThroughItsNameUnderAnOperation() {
        String parameters = "a: Int, b: Int, c: Int";
        PartitionEvidence named = guard(parameters, "let p = a + b", "Int.max(0, p) <= c");
        PartitionEvidence inline = guard(parameters, "Int.max(0, a + b) <= c");
        for (String position : List.of("a", "b", "c")) {
            assertEquals(whyAt(inline, position), whyAt(named, position), position);
        }
    }

    /**
     * Several relations each read to the end and not divided are several lines held together, and
     * stay that. Each relation on the product is a line, and where each decides turns on the
     * product, which no row is asked: nothing stopped, and no operation is named.
     */
    @Test
    void severalLinesReadToTheEndAreSeveralLinesHeldTogether() {
        assertEquals(List.of(UndividedPosition.Reason.SEVERAL_LINES_IN_ONE_RULE),
                whyAt(guard("a: Int, b: Int", "let p = a * b", "Int.max(0, p) <= 3"), "a"));
    }

    private static PartitionEvidence guard(String parameters, String condition) {
        return guard(parameters, "", condition);
    }

    private static PartitionEvidence guard(String parameters, String bound, String condition) {
        String model = """
                module demo

                data Ok
                data No

                behavior f : (%s) -> Ok | No
                let f (%s) = {
                    %s
                    guard %s else No
                    Ok
                }
                """.formatted(parameters,
                parameters.replaceAll(":\\s*[A-Za-z<>]+", ""), bound, condition);
        return measured(model);
    }

    private static PartitionEvidence measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, () -> "the model under test compiles: " + model);
        PartitionEvidence measured = coverage.get("f");
        assertNotNull(measured, () -> "f was measured: " + model);
        return measured;
    }

    /** What a report is told stopped the reading at {@code position}. */
    private static List<UndividedPosition.Reason> whyAt(PartitionEvidence measured,
                                                        String position) {
        return measured.notRead().stream()
                .filter(each -> each.at().equals(position))
                .map(PartitionEvidence.NotRead::reason)
                .toList();
    }
}
