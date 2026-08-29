package souther.compiler.check;

import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A scope answers two questions, and one answer does not serve both.
 *
 * <p>What a name means here is asked by the check, of every name a body holds. What could have been
 * written here is asked by a report offering an author what they might have meant. A call left
 * standing on a recursive helper belongs to the first and not the second: it is reached under the
 * name a method is emitted for, and that name is the library's own or another module's. The library
 * keeps {@code List.foldFrom} to itself and it stands behind every list quantifier, so it is in
 * every module's typing environment and in no module's vocabulary.
 *
 * <p>Held together in one map, it was in both — every report offering a candidate could offer a
 * caller a member the language forbids them to write.
 */
class WhatCanBeTypedHereIsNotWhatCouldHaveBeenWrittenHereTest {

    private static final Type FOLD = Type.fn(java.util.List.of(Type.INT), Type.INT);

    /** A scope as a body reaching the library's recursion is read under. */
    private static Scope standingOnTheFold() {
        return Scope.NONE.reaching(Map.of("List.foldFrom", FOLD));
    }

    @Test
    void aStandingCallOnALibraryRecursionIsTyped() {
        assertNotNull(standingOnTheFold().of(ValueName.Stdlib.operation("List", "foldFrom"),
                        "List.foldFrom"),
                "a call the expansion left standing has to be typeable where it stands");
    }

    @Test
    void andIsOfferedToNobodyAsSomethingTheyMightHaveMeant() {
        assertFalse(standingOnTheFold().spellings().contains("List.foldFrom"),
                "offered: " + standingOnTheFold().spellings());
        assertFalse(standingOnTheFold().byName().containsKey("List.foldFrom"),
                "a view keyed by what was written holds nothing nobody wrote");
    }

    /**
     * A behavior a block captured is the other kind. The author wrote its name, so it is typed here
     * and is a candidate here — which is the difference the two maps are for, rather than one of them
     * being the private half of the other.
     */
    @Test
    void aCapturedBehaviorIsBothTypeableAndSomethingAnAuthorCouldHaveWritten() {
        Scope scope = Scope.NONE.naming(Map.of("settle", FOLD));

        assertNotNull(scope.of(new ValueName.Behavior("m", "settle"), "settle"));
        assertTrue(scope.spellings().contains("settle"), "offered: " + scope.spellings());
        assertEquals(FOLD, scope.byName().get("settle"));
    }

    /** Neither displaces the other: a scope carrying both answers for both. */
    @Test
    void theTwoAreCarriedTogether() {
        Scope scope = Scope.NONE.naming(Map.of("settle", FOLD))
                .reaching(Map.of("List.foldFrom", FOLD));

        assertNotNull(scope.of(new ValueName.Behavior("m", "settle"), "settle"));
        assertNotNull(scope.of(ValueName.Stdlib.operation("List", "foldFrom"), "List.foldFrom"));
        assertEquals(java.util.List.of("settle"), scope.spellings());
    }
}
