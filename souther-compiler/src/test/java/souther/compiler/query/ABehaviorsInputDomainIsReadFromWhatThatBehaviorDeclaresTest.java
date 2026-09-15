package souther.compiler.query;

import souther.compiler.inputs.InputDomain;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What can arrive at one behavior's input is read off that behavior's declaration and off the
 * declarations its inputs reach, and off nothing else in the file.
 *
 * <p>Held per behavior, because walking one is what a reading costs. Held for the module, one was
 * walked for every behavior of it whenever anything about any of them was edited, over the whole
 * closure of what each input's declarations reach.
 *
 * <p>Three ways a behavior beside this one moves, because a body is only one of them: what it does,
 * what it states about its answer, and that it is there at all. Each arrives at a different index
 * of the module, and a reading rooted in any of them is one an edit to a behavior it says nothing
 * about takes again.
 *
 * <p>"Not read again" is the same answer object coming back, as
 * {@link AnAnswerThatCameOutTheSameLeavesItsReadersAloneTest} reads it: the store hands out what it
 * kept, so another instance is work that ran again. An equality would not say this — a reading made
 * over the same declarations and come to the same domain is exactly what this refuses.
 */
class ABehaviorsInputDomainIsReadFromWhatThatBehaviorDeclaresTest {

    private static final String MODULE = """
            module shop.orders exposing ( Code, Amount, Line, priceOf, codeOf )

            data Code = String
                invariant String.matches("[A-Z]{2}[0-9]{3}", value)
            data Amount = Int
                invariant value >= 0 && value <= 1000
            data Line = { code: Code, amount: Amount }

            behavior priceOf : (line: Line) -> Amount
            PRICE_STATES
            let priceOf (line) = PRICE

            behavior codeOf : (line: Line) -> Code
            CODE_STATES
            let codeOf (line) = CODE
            """;

    private static String with(String price, String code) {
        return MODULE.replace("PRICE_STATES\n", "").replace("CODE_STATES\n", "")
                .replace("PRICE", price).replace("CODE", code);
    }

    /** The same file, with the behavior beside this one stating a rule about its own answer. */
    private static String withTheOtherStating(String states) {
        return MODULE.replace("PRICE_STATES\n", "")
                .replace("CODE_STATES", "    ensures " + states)
                .replace("PRICE", "line.amount").replace("CODE", "line.code");
    }

    /** And the same with this behavior stating one. */
    private static String withThisStating(String states) {
        return MODULE.replace("CODE_STATES\n", "")
                .replace("PRICE_STATES", "    ensures " + states)
                .replace("PRICE", "line.amount").replace("CODE", "line.code");
    }

    /** The same file, with one more behavior declared after both of them. */
    private static String withOneMoreBehavior() {
        return with("line.amount", "line.code")
                + "\nbehavior weigh : (x: Int) -> Int\nlet weigh (x) = x\n";
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

    private static Answer<?> domainOf(Compilation c, String behavior) {
        return c.db().ask(new Adequacy.InputsOf("shop.orders", behavior));
    }

    /** And what the module hands a measure is that same reading, so the cut is what every reader of
     *  an input domain gets rather than one this test alone asks for. */
    private static InputDomain throughTheModule(Compilation c, String behavior) {
        return c.db().ask(new Adequacy.Inputs("shop.orders")).value().get(behavior);
    }

    private static void edited(Compilation c, String text) {
        c.update(Map.of(ID, text), Set.of());
        c.answerEverything();
    }

    @Test
    void anEditToAnotherBodyLeavesThisBehaviorsInputAlone() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, with("line.amount", "Code { value = line.code.value }"));

        assertSame(before, domainOf(c, "priceOf"),
                "the input domain of a behavior was walked again for an edit to another body, over"
                        + " the whole closure of what that behavior's inputs reach");
    }

    /**
     * A body is not the only thing about a behavior beside this one. What that behavior states
     * about its own answer is read into the same index, and a reading that took the index would be
     * walked again for a rule that is not about this input.
     */
    @Test
    void aRuleAnotherBehaviorStatesLeavesThisBehaviorsInputAlone() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, withTheOtherStating("value.value == line.code.value"));

        assertSame(before, domainOf(c, "priceOf"),
                "a rule another behavior states walked this behavior's input domain again");
    }

    /** And neither is a behavior declared beside it, which moves the module's index of what each
     *  of them takes and says nothing about what arrives here. */
    @Test
    void aBehaviorDeclaredBesideItLeavesThisBehaviorsInputAlone() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, withOneMoreBehavior());

        assertSame(before, domainOf(c, "priceOf"),
                "a behavior declared beside it walked this behavior's input domain again");
    }

    /**
     * And what a measure asks the module for is that kept reading, not one the assembly made of its
     * own. The module's answer is worked out again for an edit to any body in it — which behaviors
     * it has is what that answer is — and what it hands out has to be what each behavior settled.
     */
    @Test
    void theModuleHandsOutTheReadingEachBehaviorKept() {
        Compilation c = started(with("line.amount", "line.code"));
        InputDomain before = throughTheModule(c, "priceOf");

        edited(c, with("line.amount", "Code { value = line.code.value }"));

        assertSame(before, throughTheModule(c, "priceOf"),
                "the module handed a measure a reading other than the one the behavior kept");
    }

    /**
     * And an edit to this behavior's own body reads it again, which is what says the check above is
     * about where the reading is rooted and not about an answer nothing could move.
     */
    @Test
    void anEditToThisBodyReadsItAgain() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, with("Amount { value = line.amount.value }", "line.code"));

        assertNotSame(before, domainOf(c, "priceOf"),
                "this fixture cannot tell an edit the domain turns on from one it does not");
    }

    /**
     * And a rule this behavior itself states reads it again, which is what says the check above is
     * about whose rule it is and not about clauses being something the reading never takes in.
     */
    @Test
    void aRuleThisBehaviorStatesReadsItAgain() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, withThisStating("value.value <= line.amount.value"));

        assertNotSame(before, domainOf(c, "priceOf"),
                "this behavior stated a rule about a location of its input and the domain was"
                        + " kept, so this fixture says nothing about whose clauses are read");
    }

    /** And so does a declaration its input reaches stating something else. */
    @Test
    void aRuleThisInputReachesReadsItAgain() {
        Compilation c = started(with("line.amount", "line.code"));
        Answer<?> before = domainOf(c, "priceOf");

        edited(c, with("line.amount", "line.code").replace("value <= 1000", "value <= 999"));

        assertNotSame(before, domainOf(c, "priceOf"),
                "a declaration the input reaches stated something else and the domain was kept");
    }
}
