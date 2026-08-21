package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.LinkedHashSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two clauses stating one line, and both of them raise the question about it.
 *
 * <p>{@code value <= 20} and {@code value <= 10 * 2} say the same thing about which values may
 * stand at the position and about where they stop. What the model states is the same in both: an
 * ordering comparison of the position against an expression naming no position. What differs is
 * whether this compiler can fold the other side to a number, and that is a fact about this
 * compiler.
 *
 * <p>It used to decide whether the model had asked. {@code BOUNDARY} was raised out of a
 * {@code ClauseStates} arm built where {@code InvariantBound.at} came back with an end, so a clause
 * the end reading could not take in left no question standing and the accounting for it came back
 * complete. A question nothing raises is one every model answers by nobody having asked, which is
 * what {@link CoverageObligation} says of itself it is not for.
 *
 * <p>So the question is raised off the shape and the reading answers it. The pair below is the whole
 * of the difference: one line, two clauses, one question each, and one of them left standing.
 */
class AQuestionExistsBecauseTheModelStatesItAndNotBecauseAReadingSucceededTest {

    /** The clause alone, so that nothing written beside it decides the answer. */
    private static FieldDomains read(String clause) {
        String source = """
                module example.rooms

                data Length = Int
                    %s
                """.formatted(clause);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol named = TypeSymbols.declared(new TypeKey(module, "Length"));
        Hir.Data data = (Hir.Data) symbols.declarations().declaration(named.key());
        assertNotNull(data, "no `Length` declared");
        return FieldDomains.of(named, data, symbols, souther.compiler.check.ReadAs.THE_COMPILATION_DOES);
    }

    /** What the one clause of the one declaration raises. */
    private static Set<CoverageObligation> raisedBy(String clause) {
        FieldDomains domains = read(clause);
        assertEquals(1, domains.required().size(),
                () -> "one clause, one rule: " + domains.required().keySet());
        Set<CoverageObligation> out = new LinkedHashSet<>();
        domains.required().values().iterator().next().obligations()
                .forEach(owed -> out.add(owed.obligation()));
        return out;
    }

    /** The questions of that clause that nothing answered. */
    private static Set<CoverageObligation> leftStandingBy(String clause) {
        Set<CoverageObligation> out = new LinkedHashSet<>();
        read(clause).accounting().values().forEach(account ->
                account.unaccounted().forEach(owed -> out.add(owed.obligation())));
        return out;
    }

    /** What became of the line question of that clause. */
    private static RuleAccounting.Outcome lineOf(String clause) {
        return read(clause).accounting().values().stream()
                .flatMap(account -> account.answers().entrySet().stream())
                .filter(e -> e.getKey().obligation() == CoverageObligation.BOUNDARY)
                .map(java.util.Map.Entry::getValue)
                .findFirst().orElseThrow(() -> new AssertionError("no line was asked about"));
    }

    private static final Set<CoverageObligation> BOTH =
            Set.of(CoverageObligation.ADMITTED_VALUES, CoverageObligation.BOUNDARY);

    /** The line read, which is the row the other one is read against. */
    @Test
    void aBoundWrittenAsANumberRaisesTheQuestionAboutItsLineAndIsAnswered() {
        assertEquals(BOTH, raisedBy("invariant top = value <= 20"));
        assertEquals(Set.of(), leftStandingBy("invariant top = value <= 20"));
        assertInstanceOf(RuleAccounting.Outcome.Accounted.class, lineOf("invariant top = value <= 20"));
    }

    /**
     * The same line, written so that this compiler cannot fold it, asked about and left standing.
     *
     * <p>The first {@code BOUNDARY} nothing answers. What is reported is the rule the author wrote,
     * at the line it draws, with the reading that would have answered saying what stopped it — and
     * not a model that came back complete.
     */
    @Test
    void theSameLineWrittenAsAProductIsAskedAboutAndNothingAnswersIt() {
        assertEquals(BOTH, raisedBy("invariant top = value <= 10 * 2"),
                "the model states a line at 20 either way, so both are asked about");
        assertEquals(Set.of(CoverageObligation.BOUNDARY),
                leftStandingBy("invariant top = value <= 10 * 2"),
                "and the one this could not fold is the one nothing answered");

        RuleAccounting.Outcome.Unaccounted open = assertInstanceOf(
                RuleAccounting.Outcome.Unaccounted.class, lineOf("invariant top = value <= 10 * 2"));
        assertInstanceOf(RuleAccounting.Why.TheEndReadingSays.class, open.why(),
                "said by the reading that would have answered, in its own words");
    }

    /**
     * A bound the order has no value past, which is a rule read to the end and not a rule missed.
     *
     * <p>{@code value > 9223372036854775807} steps off the order: the count beside the one named is
     * one no whole number is at, so the position holds nothing. The question about its line is
     * raised and answered — the reading got there and said what the rule comes to. That no row can
     * be written there is a question about composing a row, which is existential over the whole
     * value and is no rule's to answer (#854).
     */
    @Test
    void aBoundPastWhereTheOrderStopsIsAskedAboutAndIsAnswered() {
        assertEquals(BOTH, raisedBy("invariant none = value > 9223372036854775807"));
        assertInstanceOf(RuleAccounting.Outcome.Accounted.class,
                lineOf("invariant none = value > 9223372036854775807"),
                "the reading read the rule to the end, which is the line understood");
    }

    /**
     * And the reading of values still answers for itself, in its own words.
     *
     * <p>Here so that the rows above are read against a measure that comes out the other way, and so
     * that the two vocabularies are not one. A rule nothing took in leaves its {@code ADMITTED_VALUES}
     * standing, said by the reading that turns clauses into sets of values.
     */
    @Test
    void aRuleNothingReadLeavesTheOtherQuestionStandingSaidByTheOtherReading() {
        assertEquals(Set.of(CoverageObligation.ADMITTED_VALUES),
                leftStandingBy("invariant said = Int.abs(value) >= 2"));

        RuleAccounting.Outcome.Unaccounted open =
                (RuleAccounting.Outcome.Unaccounted) read("invariant said = Int.abs(value) >= 2")
                        .accounting().values().iterator().next().answers().values().stream()
                        .filter(RuleAccounting.Outcome.Unaccounted.class::isInstance)
                        .findFirst().orElseThrow();
        assertInstanceOf(RuleAccounting.Why.TheValueReadingSays.class, open.why());
    }
}
