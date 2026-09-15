package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a count has to know about a declaration before it starts is settled by that declaration and
 * by no other.
 *
 * <p>A count rises through the answers its declarations' rules ask a collection to hold, and those
 * have to be in hand before it starts. Gathered while the count walks, every count anywhere in the
 * module read every declaration of it, whatever the edit that led to the count — and reading a
 * declaration's rules is the whole of what a count pays per declaration.
 *
 * <p>So the declarations an edit says nothing about are the ones to watch. What a declaration
 * settles is read off its own rules and off the rules of the fields it reaches, so a record holding
 * the declaration whose rule moved is reached by the edit and is settled again. What is held here
 * is everything outside that reach, however many of them the module writes.
 *
 * <p>"Not settled again" is the same answer object coming back, as
 * {@link AnAnswerThatCameOutTheSameLeavesItsReadersAloneTest} reads it. Which is what makes this a
 * check of where the count reads and not of what it came to: a premise worked out afresh and
 * compared equal is a declaration that was read, and that is the cost this is about.
 */
class ADeclarationSettlesWhatACountNeedsOfItAloneTest {

    private static final String MODULE = """
            module shop.orders exposing ( Code, Amount, Weight, Line, priceOf )

            data Code = String
                invariant String.matches("[A-Z]{2}[0-9]{3}", value)
            data Amount = Int
                invariant value >= 0 && value <= 1000
            data Weight = Int
                invariant value >= 1 && value <= 99
            data Line = { code: Code, amount: Amount, weight: Weight }

            behavior priceOf : (line: Line) -> Amount
            let priceOf (line) = line.amount
            """;

    private static String withWeightUnder(int most) {
        return MODULE.replace("value <= 99", "value <= " + most);
    }

    private static final String ID = "orders.sou";

    private static Compilation started() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put(ID, MODULE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(),
                () -> "the module compiles to begin with: " + c.db().allReports());
        return c;
    }

    private static Answer<?> premiseOf(Compilation c, String declaration) {
        return c.db().ask(
                new Shapes.CardinalityPremiseOf(new TypeKey("shop.orders", declaration)));
    }

    /**
     * One declaration's rules moving settles what the edit reaches and leaves the rest.
     *
     * <p>All of it in one test because no part of it says anything alone. That the edited
     * declaration is settled again is what says the edit reached the premises at all; that the
     * record holding it is too is where the reach ends; that the declarations outside the reach are
     * not is the claim.
     */
    @Test
    void aRuleMovingSettlesWhatItReachesAndNothingElse() {
        Compilation c = started();
        Answer<?> weight = premiseOf(c, "Weight");
        Answer<?> amount = premiseOf(c, "Amount");
        Answer<?> code = premiseOf(c, "Code");
        Answer<?> line = premiseOf(c, "Line");

        c.update(Map.of(ID, withWeightUnder(98)), Set.of());
        c.answerEverything();

        assertNotSame(weight, premiseOf(c, "Weight"),
                "the declaration whose rule moved was not settled again, so this fixture cannot"
                        + " tell a declaration an edit reached from one it did not");
        assertSame(amount, premiseOf(c, "Amount"),
                "a declaration the edit says nothing about was settled again, which is that"
                        + " declaration read again for somebody else's edit");
        assertSame(code, premiseOf(c, "Code"), "and the same for a declaration of its own rules");
        assertNotSame(line, premiseOf(c, "Line"),
                "the record holding the declaration whose rule moved was not settled again, though"
                        + " what it settles is read off the rules of the fields it reaches");
    }
}
