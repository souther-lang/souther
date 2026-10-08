package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;

import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a condition states is made where a rule concludes it and nowhere else.
 *
 * <p>A proposition built outside this package is a statement no rule of {@link Derivation} took,
 * and nothing that walks a derivation back would find the step it came from. So the census is of who
 * builds one — a record of {@link Proposition} made, or parts joined or disjoined — and it is this
 * package and no other.
 */
class APropositionIsMadeOnlyWhereARuleConcludesItTest {

    private static final String HERE = Proposition.class.getPackageName() + ".";

    /** Whoever outside this package calls {@code method} on a proposition. */
    private static Set<String> outside(String method) {
        Set<String> out = new TreeSet<>();
        for (String each : WhatWasCompiled.callersOf(Proposition.class, method)) {
            if (!each.startsWith(HERE)) {
                out.add(each);
            }
        }
        return out;
    }

    @Test
    void noPropositionIsBuiltOutsideThisPackage() {
        assertEquals(Set.of(), outside("<init>"),
                "a proposition built here is one no rule concluded");
        assertEquals(Set.of(), outside("all"), "parts joined here are joined by no rule");
        assertEquals(Set.of(), outside("any"), "parts disjoined here are disjoined by no rule");
    }

    /**
     * A meaning is a derivation concluded, and nothing else makes one: what it states beside how it
     * was derived is what that derivation concludes, by construction rather than by every maker
     * taking care.
     */
    @Test
    void aMeaningIsMadeOnlyByConcludingItsDerivation() {
        assertEquals(Set.of(Conclusion.class.getName()),
                WhatWasCompiled.callersOf(MeaningsOfABody.Meaning.class, "<init>"),
                "a meaning made elsewhere can pair a proposition with a derivation it is not the"
                        + " conclusion of");
    }

    /** And the rules do build them, so the census above counted something. */
    @Test
    void theRulesBuildThem() {
        assertTrue(WhatWasCompiled.callersOf(Proposition.class, "any")
                        .contains(Derivation.IfThenElse.class.getName()),
                "an if concludes a disjunction, and the census above sees nobody making one");
        assertTrue(WhatWasCompiled.callersOf(Proposition.class, "<init>")
                        .contains(Derivation.ATruthAtAPosition.class.getName()),
                "a truth at a position is built by its rule, and the census above sees nobody"
                        + " building one");
    }
}
