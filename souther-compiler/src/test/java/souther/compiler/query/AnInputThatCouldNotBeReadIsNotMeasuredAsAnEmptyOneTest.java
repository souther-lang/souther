package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Sig;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A behavior whose input could not be read is measured nowhere, rather than measured and found to
 * divide into nothing.
 *
 * <p>Three answers about one behavior, and they get weaker in one direction. A signature is worked
 * out from the declaration and stands whatever else in the module did not resolve. A reading of the
 * input is worked out from the declarations reaching each of its positions, and a module holding a
 * type nobody could name has none. What the model divides that input into is measured against the
 * reading, so it has none either — and the order matters: the weaker answer surviving says nothing
 * about the stronger one.
 *
 * <p>What this holds is the step from the second to the third. Asked for a reading it has not got,
 * a measure that carries on reads an input with no positions, and what comes back is a partitioning
 * that divides nothing. Nothing in it says the reading was missing: a behavior whose every position
 * went unread reports exactly as one whose positions the rules part nowhere, and the report says it
 * went without nothing.
 */
class AnInputThatCouldNotBeReadIsNotMeasuredAsAnEmptyOneTest {

    /**
     * A module whose import did not resolve, so a field of one of its records has a type nobody
     * could name.
     *
     * <p>{@code receipt} is the behavior this is about. Its own parameter is a record declared
     * here, so its signature is worked out and it is not a behavior the analysis left out — while
     * the module it is declared in holds a hole, which is what the input's reading is refused for.
     */
    private static final String UNRESOLVED = """
            module probe.unread
            import shared.money ( Amount )

            data Invoice = { amount: Amount }
            data Receipt = { n: Int }

            behavior receipt : (i: Invoice) -> Receipt
                constructs Receipt
            let receipt (i) = Receipt { n = 1 }
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(UNRESOLVED, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    /** The signature is in hand, which is the weakest of the three and the one that survives. */
    @Test
    void theSignatureIsWorkedOutAllTheSame() {
        Map<String, Sig> sigs =
                measured().db().ask(new Bodies.Signatures("probe.unread")).value();
        assertNotNull(sigs, "the signatures answered");
        assertTrue(sigs.containsKey("receipt"),
                "a behavior whose own declaration resolves has its boundary worked out");
    }

    /** The reading is not, because the module holds a type nobody could name. */
    @Test
    void theInputIsNotRead() {
        assertNull(measured().db().ask(new Adequacy.Inputs("probe.unread")).value(),
                "a module with a hole in it has no reading of what its behaviors take");
    }

    /**
     * And nothing publishes a measurement of an input that was never read.
     *
     * <p>The step this exists for. A partitioning here would be one measured against no positions,
     * and every reader of it is told the model divides this behavior nowhere — which is what a
     * behavior whose rules part nothing is told, and the two are not the same behavior.
     */
    @Test
    void andSoNothingSaysWhatTheModelDividesItInto() {
        assertNull(measured().db().ask(new Adequacy.Divided("probe.unread", "receipt")).value(),
                "an input with no reading is measured nowhere, not measured into nothing");
    }
}
