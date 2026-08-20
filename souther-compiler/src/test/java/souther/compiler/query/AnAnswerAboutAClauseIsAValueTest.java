package souther.compiler.query;

import souther.compiler.check.StatedContract;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a query answers about a clause is a value, so asking twice about one source answers the same
 * thing twice.
 *
 * <p>{@code Db} stops work by comparing an answer with the one it replaces: "an answer that never
 * equals the one it replaces leaves nothing standing". So anything reachable from an answer has to
 * mean something by {@code equals}, and a run-specific object means only itself.
 *
 * <p>It is a clause whose typing does not finish that this is about. What such a clause typed to
 * used to be an exception object, and two runs over one unedited source then answered with two
 * contracts that were never equal — so every unrelated edit re-ran everything downstream of them,
 * for as long as the source stayed half-written, which is most of the time an editor is asking.
 */
class AnAnswerAboutAClauseIsAValueTest {

    /** A rule over a name that is not a standard-library function, so typing the rule does not
     *  finish and the conjunct comes back as one nothing was made of. */
    private static final String STOPS = """
            module m.a exposing ( Found, findIt )

            data Found = { id: Int }

            behavior findIt : (id: Int) -> Found
                constructs Found
                ensures Int.toWords(value.id) == "one"

            let findIt (id) = Found { id = id }
            """;

    private static final String READS = """
            module m.a exposing ( Found, findIt )

            data Found = { id: Int }

            behavior findIt : (id: Int) -> Found
                constructs Found
                ensures value.id >= 0

            let findIt (id) = Found { id = id }
            """;

    private static Map<String, StatedContract> contractsOf(String source) {
        Compilation c = Compilation.ofDocuments(Map.of("a.sou", source), Set.of(), ModulePath.EMPTY);
        return c.db().ask(new Bodies.StatedContracts("m.a")).value();
    }

    @Test
    void aRuleWhoseTypingDidNotFinishAnswersTheSameTwice() {
        Map<String, StatedContract> once = contractsOf(STOPS);
        Map<String, StatedContract> again = contractsOf(STOPS);

        assertNotNull(once, "the module reads, so its behaviors are stated");
        assertEquals(once, again, "one source, one answer — whatever the typing did");
    }

    /** And the ordinary case, so that the one above is not passing because nothing was answered. */
    @Test
    void aRuleThatTypesAnswersTheSameTwice() {
        assertEquals(contractsOf(READS), contractsOf(READS));
    }

    /** Two different sources do not answer alike, so the equality above is saying something. */
    @Test
    void twoSourcesDoNotAnswerAlike() {
        assertEquals(false, contractsOf(STOPS).equals(contractsOf(READS)),
                "a rule nothing was made of and a rule read as a bound are different answers");
    }
}
