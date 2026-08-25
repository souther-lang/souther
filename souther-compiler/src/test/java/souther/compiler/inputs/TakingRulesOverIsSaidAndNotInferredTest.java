package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A reading that ends with rules under it still to be read is discharged by something saying it
 * took them, and never by something being there.
 *
 * <p>The defect this is written against was the other reading of the same evidence. A position was
 * called short of its rules because a rule stood somewhere under its type, and the walk had gone to
 * that rule one position down — so the shortfall was worked out from the type graph rather than from
 * what the walk did (#1072). Repaired by asking whether a reading exists under the path, it would be
 * the same mistake pointed the other way: a reading opened under the position for some other reason
 * would discharge an obligation it never heard of, and "no failure is visible here" would again be
 * standing in for "everything was read".
 *
 * <p>So the three things below are what a discharge is. Something has to have been passed the rules,
 * everything that was passed them has to have been opened, and opening them is the whole of it — a
 * reading that took the rules over and then came back short of something reports that itself, at its
 * own position, and reporting it again above would be one gap counted at two places.
 */
class TakingRulesOverIsSaidAndNotInferredTest {

    private static final TermPath P = TermPath.of("p");
    private static final TermPath HANDS_ON = P.then("x");

    /**
     * A reading opened somewhere nobody handed anything to discharges nothing.
     *
     * <p>Refused rather than ignored. A descent that opens a reading at a position the handoff never
     * named is a descent disagreeing with the one that enumerated the children, and the two are the
     * same walk — so this is a fault in the compiler and not a state of the model.
     */
    @Test
    void aReadingNobodyPassedTheRulesToDischargesNothing() {
        RuleHandoffs handoffs = new RuleHandoffs();
        handoffs.owes(P, HANDS_ON);
        handoffs.passesTo(P, HANDS_ON, List.of(HANDS_ON.element()));

        assertThrows(IllegalArgumentException.class,
                () -> handoffs.accepts(P, HANDS_ON, P.then("y")),
                "a reading at a position this handoff never named is not one it passed rules to");
        assertTrue(handoffs.unresolvedAt(HANDS_ON),
                "and the handoff is where it was");
    }

    /** And a handoff no descent ever reached stands however many readings were opened elsewhere. */
    @Test
    void aHandoffNoDescentReachedStandsWhateverElseWasRead() {
        RuleHandoffs handoffs = new RuleHandoffs();
        handoffs.owes(P, HANDS_ON);
        TermPath elsewhere = P.then("y");
        handoffs.owes(P, elsewhere);
        handoffs.passesTo(P, elsewhere, List.of(elsewhere.element()));
        handoffs.accepts(P, elsewhere, elsewhere.element());

        assertFalse(handoffs.unresolvedAt(elsewhere), "that one was passed on and taken");
        assertTrue(handoffs.unresolvedAt(HANDS_ON),
                "and this one was never passed to anybody, whatever happened beside it");
    }

    /**
     * Every position the rules were passed to has to have been opened, and not merely one of them.
     *
     * <p>A sum passes the rules of each case to that case. A case nothing walked has left the rules
     * written on it unread however well the case beside it went, and a handoff counted as met by the
     * first reading to arrive would say the sum had been read to the end.
     */
    @Test
    void aHandoffIsMetOnlyWhenEveryPositionItPassedToWasOpened() {
        RuleHandoffs handoffs = new RuleHandoffs();
        handoffs.owes(P, HANDS_ON);
        TermPath one = HANDS_ON.then("a");
        TermPath other = HANDS_ON.then("b");
        handoffs.passesTo(P, HANDS_ON, List.of(one, other));

        handoffs.accepts(P, HANDS_ON, one);
        assertTrue(handoffs.unresolvedAt(HANDS_ON), "the other case was passed the rules too");

        handoffs.accepts(P, HANDS_ON, other);
        assertFalse(handoffs.unresolvedAt(HANDS_ON), "and now both of them were opened");
    }

    /**
     * One position, one reading answering for its rules.
     *
     * <p>Which reading that is follows from where the descent last crossed an ownership boundary, so
     * it is a function of the path. Everything here carries the pair and one step does not:
     * {@link RuleHandoffs#unresolvedAt} asks by position alone. That projection is safe only while
     * this holds, so it is refused rather than assumed — a handoff owed by a reading nobody kept
     * would otherwise leave somebody else's position short, which is this issue's own shape.
     */
    @Test
    void twoReadingsCannotAnswerForTheRulesAtOnePosition() {
        RuleHandoffs handoffs = new RuleHandoffs();
        handoffs.owes(P, HANDS_ON);

        handoffs.owes(P, HANDS_ON);

        assertThrows(IllegalStateException.class,
                () -> handoffs.owes(P.then("elsewhere"), HANDS_ON),
                "a second reading answering for one position is this walk contradicting itself");
    }

    /** A value whose own clause could not be typed, held behind an optional. What is short is the
     *  reading of that value, and the optional above it handed the rules to exactly that reading. */
    private static final String THE_READING_OPENED_IS_SHORT = """
            module example.short

            data Inner = String
                invariant no = value == 1

            data P = { x: Inner? }

            data Taken

            behavior take : (p: P) -> Taken
            """;

    /**
     * Handing the rules over is not the same as reading them.
     *
     * <p>The reading opened at the narrowing is short of {@code Inner}'s own clause, which nothing
     * could type. That is reported where it happened, and the position that passed the rules to it is
     * short of nothing: the rules reached a reader, and saying so again above would be one gap
     * counted at two positions and named at the one an author cannot act on.
     */
    @Test
    void aReadingThatTookTheRulesOverAndCameBackShortIsShortByItself() {
        InputDomain read = read(THE_READING_OPENED_IS_SHORT);

        assertFalse(read.at(TermPath.of("p").then("x")).rulesNotReached(),
                "the optional passed the rules on and something took them");
        assertTrue(shortSomewhereUnder(read, TermPath.of("p").then("x")),
                "and the reading that took them says what it could not read");
    }

    private static boolean shortSomewhereUnder(InputDomain read, TermPath above) {
        return read.positions().stream()
                .anyMatch(each -> !each.path().equals(above)
                        && each.path().toString().startsWith(above.toString())
                        && each.rulesNotReached());
    }

    private static InputDomain read(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("take")).findFirst().orElseThrow();
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain read = InputDomain.of(spec, sigs.get("take"), symbols,
                ReadAs.THE_COMPILATION_DOES);
        assertNotNull(read, "the model under test compiles");
        return read;
    }
}
