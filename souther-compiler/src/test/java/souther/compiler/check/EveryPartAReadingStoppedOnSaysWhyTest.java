package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
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

/**
 * A question stands with every reason it stands for, and not with the first of them.
 *
 * <p>One clause names one position in as many parts as its author wrote about it, and two of those
 * parts stop the reading of values in two ways: a relation between two positions is a rule this
 * reading recognised and has no set of one position's values for, and a pattern is a form it does
 * not take apart at all. The two are lifted by different work and a report writes a different word
 * for each.
 *
 * <p>Held as one reason, which of them an author was shown turned on the order the parts were met
 * in, and the other was gone with nothing saying so. So this asks for both, and asks for them in
 * the order the clause writes them: an answer that came out as a set would be the same assertion
 * with the order left to whatever a hash happened to do.
 */
class EveryPartAReadingStoppedOnSaysWhyTest {

    /** A relation and a pattern about one position, in one clause. */
    private static final String TWO_PARTS_AT_ONE_POSITION = """
            module demo

            data N = { a: String, b: String }
                invariant both = a /= b && String.startsWith("x", a)
            """;

    /** The two written the other way round, which is the same clause. */
    private static final String THE_OTHER_ORDER = """
            module demo

            data N = { a: String, b: String }
                invariant both = String.startsWith("x", a) && a /= b
            """;

    /**
     * Two rules about the one position, stopped in two ways.
     *
     * <p>{@code shape} is a form this reading does not take apart. {@code either} it reads in full
     * on the side that names {@code a} and not on the side beside it, so what {@code a} is left
     * with is that an alternative went unread — a value satisfying the branch nothing read owes the
     * branch that was read nothing. Two rules, two limits, one position.
     */
    private static final String TWO_RULES_AT_ONE_POSITION = """
            module demo

            data N = { a: String, b: String }
                invariant shape = String.startsWith("x", a)
                invariant either = a == "q" || String.startsWith("x", b)
            """;

    /**
     * Two conjuncts drawing one line, each of them stopped.
     *
     * <p>Both are bounds on {@code x} whose other side is not a form a threshold is read out of, so
     * both ask the one question about the line on {@code x} and the reading of ends was stopped on
     * each of them. The two are recorded apart, at the conjunct each came from.
     */
    private static final String TWO_CONJUNCTS_ON_ONE_LINE = """
            module demo

            data N = { x: Int, y: Int }
                invariant said = x <= 10 * 2 && x <= Int.abs(x)
            """;

    /**
     * A clause about a position none of the readings knows.
     *
     * <p>The invariant is a call, and what it comes to is a rule about a field of the value the
     * helper was handed. The readings here are filed under the positions they recognise, and that
     * field is not one of them — so the rule is claimed by none of them, and none of them has
     * anything to say about why.
     */
    private static final String A_RULE_NO_READING_CLAIMS = """
            module demo

            data Range = { min: Int, max: Int }

            data N = { range: Range }
                invariant valid(range)

            let valid (r: Range) : Bool = r.max >= 0
            """;

    /** What became of every question of every rule that nothing answered. */
    private static Map<String, String> whyStanding(FieldDomains read) {
        Map<String, String> out = new LinkedHashMap<>();
        read.accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted) {
                        out.put(((RuleCitation.Named) accounting.cited()).name() + " at " + owed,
                                unaccounted.why().getClass().getSimpleName());
                    }
                }));
        return out;
    }

    /**
     * A question no reading claimed says so, and does not borrow a reading's account.
     *
     * <p>The other two arms are one reading's own words for where it gave up. A question standing
     * because nobody took the rule in has no such words behind it — answered with them, an author
     * is told which reader fell short of their clause, and the reader named is one that never held
     * it and has no word for such a rule at all.
     */
    @Test
    void aQuestionNoReadingClaimedNamesNoReading() {
        assertEquals(Map.of("invariant N #1 at range.max", "NothingTookItIn"),
                whyStanding(read(A_RULE_NO_READING_CLAIMS)));
    }

    /** Everything the reading of ends was stopped by, per question it left standing. */
    private static Map<String, List<String>> linesStanding(FieldDomains read) {
        Map<String, List<String>> out = new LinkedHashMap<>();
        read.accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted
                            && unaccounted.why()
                                    instanceof RuleAccounting.Why.TheEndReadingSays says) {
                        out.put(((RuleCitation.Named) accounting.cited()).name() + " at " + owed,
                                says.why().stream()
                                        .map(each -> each.getClass().getSimpleName()).toList());
                    }
                }));
        return out;
    }

    /**
     * A line stands on every conjunct that was stopped behind it, and says one limit once.
     *
     * <p>Both halves. The reading of ends was stopped on each of the two conjuncts and recorded
     * each of them, which is what the first assertion reads: the question is answered when every
     * conjunct that draws the line has been read, so a conjunct standing behind another is a second
     * thing to lift and not something the first answers for.
     *
     * <p>And the answer names the limit once. What a reader is owed is what to lift, and two
     * conjuncts a single limit stopped are one thing to lift — said twice, an author would be shown
     * their own rule as two.
     */
    @Test
    void aLineStandsOnEveryConjunctStoppedBehindIt() {
        FieldDomains read = read(TWO_CONJUNCTS_ON_ONE_LINE);

        assertEquals(2, read.noLineAt("x").size(),
                "each conjunct was stopped, and each is recorded where it was written");
        assertEquals(List.of("UnreadComparisonForm"),
                linesStanding(read).get("invariant N (said) at x"));
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
        return FieldDomains.of(name,
                (Hir.Data) symbols.declarations().declaration(name.key()), symbols,
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }

    /** What the reading of values was stopped by, over every question of every rule of the value. */
    private static List<UnreadReason> stoppedBy(FieldDomains read) {
        return read.accounting().values().stream()
                .flatMap(each -> stoppedBy(each).stream())
                .toList();
    }

    /** The same, of one rule. */
    private static List<UnreadReason> stoppedBy(RuleAccounting accounting) {
        return accounting.answers().values().stream()
                .filter(RuleAccounting.Outcome.Unaccounted.class::isInstance)
                .map(each -> ((RuleAccounting.Outcome.Unaccounted) each).why())
                .filter(RuleAccounting.Why.TheValueReadingSays.class::isInstance)
                .flatMap(each -> ((RuleAccounting.Why.TheValueReadingSays) each).why().stream())
                .toList();
    }

    /**
     * Every question of every rule that nothing answered, and what stopped this reading of it.
     *
     * <p>Keyed by the rule and the subject together, which is what a question is. One rule raises a
     * question about every position it names, and a helper folding them together would report a
     * rule answered for at one position with the limit it met at another.
     */
    private static Map<String, List<UnreadReason>> byQuestion(FieldDomains read) {
        Map<String, List<UnreadReason>> out = new LinkedHashMap<>();
        read.accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (outcome instanceof RuleAccounting.Outcome.Unaccounted unaccounted
                            && unaccounted.why()
                                    instanceof RuleAccounting.Why.TheValueReadingSays says) {
                        out.put(((RuleCitation.Named) accounting.cited()).name() + " at " + owed,
                                says.why());
                    }
                }));
        return out;
    }

    /** Both parts say why, and neither stands in for the other. */
    @Test
    void aQuestionStandsWithEveryReasonItStandsFor() {
        assertEquals(
                List.of(UnreadReason.RELATES_TWO_POSITIONS, UnreadReason.FORM_NOT_READ),
                stoppedBy(read(TWO_PARTS_AT_ONE_POSITION)));
    }

    /**
     * And in the order the clause writes them.
     *
     * <p>The two assertions together are what says the reasons are not a set. Asked of one order
     * only, a reading that sorted them or held them in a hash would pass — and an author reading
     * their own rules back would meet them in an order nothing in their model decides.
     */
    @Test
    void andInTheOrderTheClauseWritesThem() {
        assertEquals(
                List.of(UnreadReason.FORM_NOT_READ, UnreadReason.RELATES_TWO_POSITIONS),
                stoppedBy(read(THE_OTHER_ORDER)));
    }

    /**
     * Each rule is answered for by what stopped this reading of that rule.
     *
     * <p>Two limits at one position, met by two rules. Answered from the position, each of them is
     * told about the limit its neighbour met as well — and an author sent to rewrite {@code either}
     * is told their clause is written in a form this compiler does not read, which is false of it
     * and true of the rule beside it.
     */
    @Test
    void aRuleIsAnsweredForByWhatStoppedThatRule() {
        assertEquals(
                Map.of("invariant N (shape) at a", List.of(UnreadReason.FORM_NOT_READ),
                        "invariant N (either) at a", List.of(UnreadReason.ALTERNATIVE_NOT_READ),
                        // The other position the second rule names, which is where the branch this
                        // reading has no word for is written.
                        "invariant N (either) at b", List.of(UnreadReason.FORM_NOT_READ)),
                byQuestion(read(TWO_RULES_AT_ONE_POSITION)));
    }
}
