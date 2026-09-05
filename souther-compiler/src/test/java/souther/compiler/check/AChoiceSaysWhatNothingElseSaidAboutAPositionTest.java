package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.UnreadReason;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A choice is answerable for a position its unread alternative said nothing else about.
 *
 * <p>What an alternative nothing could read does is leave the positions the other branch promised
 * open. At a position that branch is already answerable for something, that is the same shortfall
 * arriving by another road — a form nothing reads is one thing to lift, and a reader told to lift
 * it and then told about the choice above it would lift the form and find the question still there.
 * At a position the branch never named, the choice is the first thing to say anything.
 *
 * <p><b>Asked of what the branch is answerable for, and never of what the position holds.</b> A
 * place holds the reasons of every rule that reached it, so a rule suppressed by it would be a fact
 * about a rule turning on what a neighbour wrote. The position's own account has a rule of its own
 * that comes to the same answer here, and the two are two rules ({@code UnreadReason.leftOpen}).
 *
 * <p>Which choice, because that is what it is a fact about. Filed at a leaf under the branch that
 * was read, an author would be sent to a clause nothing complained of.
 */
class AChoiceSaysWhatNothingElseSaidAboutAPositionTest {

    /**
     * A branch nothing reads, beside one that promises a position it never names.
     *
     * <p>The unread side is about {@code a}; {@code b} is promised by the other side and appears
     * nowhere in the branch that was not read, so nothing but the choice has anything to say about
     * why {@code b} is open.
     */
    private static final String NOTHING_ELSE_SAID_ABOUT_IT = """
            module demo

            data N = { a: String, b: String }
                invariant r = UNREAD_A || b == "A"
            """.replace("UNREAD_A", souther.compiler.ARuleNoReadingTakesIn.about("a"));

    /** And one where the branch nothing reads is about the position itself. */
    private static final String THE_BRANCH_SAID_IT_ITSELF = """
            module demo

            data N = { a: String }
                invariant r = a == "A" || UNREAD_A
            """.replace("UNREAD_A", souther.compiler.ARuleNoReadingTakesIn.about("a"));

    /** Two choices of one rule, each leaving one position open and neither naming it. */
    private static final String TWO_CHOICES_LEAVE_IT_OPEN = """
            module demo

            data N = { a: String, b: String, c: String }
                invariant r =
                    (UNREAD_A || c == "A") && (UNREAD_B || c == "A")
            """.replace("UNREAD_A", souther.compiler.ARuleNoReadingTakesIn.about("a"))
            .replace("UNREAD_B", souther.compiler.ARuleNoReadingTakesIn.about("b"));

    /** The same unreadness under one more bracket, which is one connective and not a tree. */
    private static final String THE_SAME_THROUGH_ONE_MORE_BRACKET = """
            module demo

            data N = { a: String, b: String }
                invariant r = b == "A" || (b == "B" || UNREAD_A)
            """.replace("UNREAD_A", souther.compiler.ARuleNoReadingTakesIn.about("a"));

    /** And the same disjunction bracketed the other way, which says what a bracket is not. */
    private static final String THE_SAME_BRACKETED_THE_OTHER_WAY = """
            module demo

            data N = { a: String, b: String }
                invariant r = (b == "A" || b == "B") || UNREAD_A
            """.replace("UNREAD_A", souther.compiler.ARuleNoReadingTakesIn.about("a"));

    /** Where nothing else said anything about the position, the choice says it. */
    @Test
    void aChoiceIsAnswerableWhereItsUnreadAlternativeSaidNothing() {
        assertEquals(Set.of(UnreadReason.ALTERNATIVE_NOT_READ),
                whatARuleIsAnswerableFor(NOTHING_ELSE_SAID_ABOUT_IT, "b"),
                "the branch that was not read never names this position, so the choice is the"
                        + " first thing with anything to say about why it is open");
    }

    /** And where the branch said it itself, the choice adds nothing. */
    @Test
    void aChoiceAddsNothingWhereItsUnreadAlternativeSaidItAlready() {
        assertEquals(Set.of(UnreadReason.FORM_NOT_READ),
                whatARuleIsAnswerableFor(THE_BRANCH_SAID_IT_ITSELF, "a"),
                "one form nothing reads is one thing to lift, and the choice above it is the same"
                        + " shortfall arriving by another road");
    }

    /** And two choices leaving one position open are two things to look at. */
    @Test
    void twoChoicesLeavingOnePositionOpenAreBothAnswerable() {
        assertEquals(2, sitesFor(TWO_CHOICES_LEAVE_IT_OPEN, "c").size(),
                "each choice offered an alternative of its own, and an author has both to look"
                        + " at — held as reasons at the position they were one");
    }

    /** And one more bracket around the same unreadness is not one more thing to look at. */
    @Test
    void oneMoreBracketIsNotOneMoreThingToLookAt() {
        assertEquals(1, sitesFor(THE_SAME_THROUGH_ONE_MORE_BRACKET, "b").size(),
                "a choice is one connective and not a tree, so a shortfall that passed through a"
                        + " bracket on its way up is not a second shortfall");
    }

    /**
     * And bracketing the same disjunction the other way says the same thing.
     *
     * <p>Which is what a bracket not being a second shortfall comes to: the reasons are of the
     * choices an author wrote, and {@code ||} means the same thing however it was grouped. Two
     * choices are still two — what is held here is that grouping alone makes neither.
     */
    @Test
    void theSameDisjunctionGroupedTheOtherWaySaysTheSame() {
        assertEquals(whatARuleIsAnswerableFor(THE_SAME_THROUGH_ONE_MORE_BRACKET, "b"),
                whatARuleIsAnswerableFor(THE_SAME_BRACKETED_THE_OTHER_WAY, "b"),
                "a reader is told the same thing whichever way the author grouped the choice");
        assertEquals(sitesFor(THE_SAME_THROUGH_ONE_MORE_BRACKET, "b").size(),
                sitesFor(THE_SAME_BRACKETED_THE_OTHER_WAY, "b").size(),
                "and has the same number of things to look at");
    }

    /** What a rule of the declaration is answerable for at {@code field}. */
    private static Set<UnreadReason> whatARuleIsAnswerableFor(String source, String field) {
        Set<UnreadReason> out = new LinkedHashSet<>();
        shortfallsAt(source, field).forEach(each -> out.add(each.why()));
        return out;
    }

    /** The written places it is answerable at, which is what tells two of them apart. */
    private static Set<RuleShortfall.Site> sitesFor(String source, String field) {
        Set<RuleShortfall.Site> out = new LinkedHashSet<>();
        shortfallsAt(source, field).forEach(each -> out.add(each.site()));
        return out;
    }

    /**
     * What every question about {@code field} is answerable for, over every rule of the value.
     *
     * <p>Keyed by the question and not by the position inside a shortfall: a question is of one rule
     * at one position, and what is filed under it is that position's. Read the other way, this test
     * would be reading a place's reasons to find a rule's, which is the thing being closed.
     */
    private static Set<RuleShortfall> shortfallsAt(String source, String field) {
        Set<RuleShortfall> out = new LinkedHashSet<>();
        read(source).accounting().values().forEach(accounting ->
                accounting.answers().forEach((owed, outcome) -> {
                    if (owed.toString().equals(field)
                            && outcome instanceof RuleAccounting.Outcome.Unaccounted it
                            && it.why() instanceof RuleAccounting.Why.TheValueReadingSays says) {
                        out.addAll(says.shortfalls());
                    }
                }));
        return out;
    }

    private static FieldDomains read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                .flatMap(List::stream).map(each -> each.diagnostic().code()).toList(),
                "the model this reads has to be one somebody could write");
        Symbols symbols = Scopes.derived(compilation.db(), "demo").value();
        TypeSymbol.AtModule name = TypeSymbols.declared(new TypeKey(symbols.module(), "N"));
        return FieldDomains.of(name, RuleReadings.of(compilation, "demo"),
                souther.compiler.query.ReadAs.THE_COMPILATION_DOES);
    }
}
