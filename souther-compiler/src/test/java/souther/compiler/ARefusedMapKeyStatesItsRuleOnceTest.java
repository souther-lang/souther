package souther.compiler;

import souther.compiler.check.TypeOps;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Note;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A Map key is refused in three places — a data's field, a behavior's input, a behavior's output —
 * and there is one rule behind all three. Each used to describe it in its own words, and the copies
 * drifted: the enumeration became an admitted key (issue #161) and only the catalog was told, so
 * three of the sentences went on listing four kinds.
 *
 * <p>So the rule is stated once and the sites point at it. What each site says of its own is where
 * the key sits; what the rule is, is not theirs to word.
 */
class ARefusedMapKeyStatesItsRuleOnceTest {

    private static final String FIELD = """
            module demo

            data EmployeeNo = Int
            data Roster = { byNo: Map<EmployeeNo, String> }
            data Out = { count: Int }

            behavior count : (r: Roster) -> Out constructs Out

            let count (r) = Out { count = 0 }
            """;

    private static final String PARAM = """
            module demo

            data EmployeeNo = Int
            data Out = { count: Int }

            behavior count : (byNo: Map<EmployeeNo, String>) -> Out constructs Out

            let count (byNo) = Out { count = 0 }
            """;

    private static final String OUTPUT = """
            module demo

            data EmployeeNo = Int
            data In = { n: Int }

            behavior widen : (i: In) -> Map<EmployeeNo, String> constructs EmployeeNo

            let widen (i) = Map.empty
            """;

    private static CompileException refusal(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }

    private static String hintKey(CompileException e) {
        List<Note> notes = e.diagnostic().notes();
        assertEquals(1, notes.size(), e.getMessage());
        return notes.get(0).messageKey();
    }

    /** One rule, one place it is written down. Three hint keys were three chances to say it
     *  differently, and one of them was already saying something else. */
    @Test
    void theThreeSitesPointAtOneStatementOfTheRule() {
        assertEquals(hintKey(refusal(FIELD)), hintKey(refusal(PARAM)));
        assertEquals(hintKey(refusal(PARAM)), hintKey(refusal(OUTPUT)));
    }

    /** The sentence a Java caller reads is the same rule, taken from the one place it is written
     *  rather than restated per site. A fourth site wording it itself fails here. */
    @Test
    void eachSiteCarriesTheRuleItWasGivenRatherThanItsOwn() {
        for (String source : List.of(FIELD, PARAM, OUTPUT)) {
            String message = refusal(source).getMessage();
            assertTrue(message.contains("A Map is a JSON object, whose keys are strings"), message);
        }
    }
}
