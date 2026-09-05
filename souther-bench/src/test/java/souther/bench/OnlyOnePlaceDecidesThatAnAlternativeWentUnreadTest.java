package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * That a choice offered an alternative nothing could read is decided in one place.
 *
 * <p>Two things are owed about it and they are not the same thing. A position has to be told that
 * it may be wider than the rules leave it, and the account of a rule has to send an author to the
 * choice they wrote. Both are projections of one decision — which alternative went unread and what
 * the one beside it left — and the decision can only be made where the alternatives are what stands
 * between the brackets, because a conjunction written beside a choice is distributed into both of
 * them before the values are worked out.
 *
 * <p>So each side receiving the answer is the shape being held. Read off the call sites, because
 * that is what the rule is about: nothing in a type stops a carrier that holds two branches and a
 * flag from working out for itself which positions a choice opened, and that is the arrangement
 * this closes.
 */
class OnlyOnePlaceDecidesThatAnAlternativeWentUnreadTest {

    private static final String OPENING = "souther.compiler.check.StatedByClauses$AlternativeOpening";

    /** The one method that answers what a choice left open, out of what its alternatives took in. */
    private static final String AUTHORITY =
            "souther.compiler.check.StatedByClauses#opens"
                    + "(Lsouther/compiler/check/ChoiceId;Lsouther/compiler/check/Adoption;"
                    + "Lsouther/compiler/check/Adoption;)"
                    + "Lsouther/compiler/check/StatedByClauses$AlternativeOpening;";

    /**
     * One method decides one, and it is that one.
     *
     * <p>The class is not the boundary. Two methods of it, each working the answer out for the
     * caller in front of them, are the arrangement this closes — the position and the account of
     * the rule had exactly that, and agreed only until a conjunction stood beside a choice.
     */
    @Test
    void oneMethodDecidesWhatAChoiceLeftOpen() throws Exception {
        List<String> made = new ArrayList<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.makesA(OPENING)) {
                made.add(site.at());
            }
        }

        assertEquals(List.of(AUTHORITY), made.stream().distinct().sorted().toList(),
                "which positions a choice left open is answered somewhere else as well, or nowhere"
                        + " — and a second answer holds only until a conjunction stands beside a"
                        + " choice and the two are asked of different branches");
    }
}
