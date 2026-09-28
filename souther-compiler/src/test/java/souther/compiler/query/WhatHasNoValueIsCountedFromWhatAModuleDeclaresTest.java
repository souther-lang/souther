package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of a module's declarations no value satisfies is settled by what the module declares and by
 * what those declarations state, and by nothing else in the file.
 *
 * <p>What the count is taken over is the types the module writes; what each of them comes to is
 * what its rules leave. A body is neither. Taken over the module as the passes below it leave it,
 * the count was asked again for an edit to any line of the file — and asking it again is reading
 * every declaration the module reaches, so a keystroke in a body cost the reading of every type
 * beside it.
 *
 * <p>"Not taken again" is the same answer object coming back, which is how
 * {@link AnAnswerThatCameOutTheSameLeavesItsReadersAloneTest} reads it: the store hands out what it
 * kept, so another instance is work that ran again. An equality on the answer would not say this —
 * a count that ran and came to the same groups is exactly what this is here to refuse.
 */
class WhatHasNoValueIsCountedFromWhatAModuleDeclaresTest {

    private static final String MODULE = """
            module shop.orders exposing ( Code, Amount, Line, priceOf )

            data Code = String
                invariant String.matches("[A-Z]{2}[0-9]{3}", value)
            data Amount = Int
                invariant value >= 0 && value <= 1000
            data Line = { code: Code, amount: Amount }

            behavior priceOf : (line: Line) -> Amount
            let priceOf (line) = BODY
            """;

    /** The same declarations, with the one body written another way. */
    private static String withBody(String expression) {
        return MODULE.replace("BODY", expression);
    }

    /** The same body, with one declaration stating something else. */
    private static String withAmountUnder(int most) {
        return withBody("line.amount").replace("value <= 1000", "value <= " + most);
    }

    private static final String ID = "orders.sou";

    private static Compilation started(String text) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(ID, text);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        return c;
    }

    private static Answer<?> counted(Compilation c) {
        return c.db().ask(new Shapes.TypesWithNoValue("shop.orders"));
    }

    private static void edited(Compilation c, String text) {
        c.update(Map.of(ID, text), Set.of());
        c.answerEverything();
    }

    /** A body written another way leaves the count where it was: it says nothing about which types
     *  the module declares, and nothing about what any of them states. */
    @Test
    void anEditToABodyDoesNotTakeTheCountAgain() {
        Compilation c = started(withBody("line.amount"));
        Answer<?> before = counted(c);

        edited(c, withBody("Amount { value = line.amount.value }"));

        assertSame(before, counted(c),
                "the count of what has no value was taken again for an edit to a body, which"
                        + " reads every declaration the module reaches");
    }

    /**
     * And a rule stating something else takes it again, which is what says the check above is about
     * the body and not about an answer nothing could move.
     */
    @Test
    void anEditToARuleTakesTheCountAgain() {
        Compilation c = started(withBody("line.amount"));
        Answer<?> before = counted(c);

        edited(c, withAmountUnder(999));

        assertNotSame(before, counted(c),
                "a declaration stating something else left the count where it was, so this fixture"
                        + " cannot tell an edit the count turns on from one it does not");
    }
}
