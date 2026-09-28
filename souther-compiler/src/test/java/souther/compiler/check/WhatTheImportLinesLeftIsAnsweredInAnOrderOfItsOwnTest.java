package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The order the namespaces an import line contributes to come back in.
 *
 * <p>What each spelling settled as is a mapping, and the four namespaces are read off it by walking
 * it. The order that walk went in was whatever the pass assembling the spellings handed them over
 * in — which is no answer about a module's imports, and it was reaching the four answers through
 * the containers they were filled into. Each of them is ordered by the spelling it is keyed on now,
 * so what comes back is a function of what it holds.
 */
class WhatTheImportLinesLeftIsAnsweredInAnOrderOfItsOwnTest {

    /** The same imports settled in either order answer in one order. */
    @Test
    void theOrderTheSpellingsWereSettledInIsNoPartOfWhatComesBack() {
        ResolvedImports oneWay = imports("c", "a", "b");
        ResolvedImports theOther = imports("b", "c", "a");

        assertEquals(List.copyOf(oneWay.types().keySet()),
                List.copyOf(theOther.types().keySet()),
                "the type namespace comes back in one order whichever way it was assembled");
        assertEquals(List.copyOf(oneWay.values().keySet()),
                List.copyOf(theOther.values().keySet()),
                "and so does the value namespace");
        assertEquals(List.of("a", "b", "c"), List.copyOf(oneWay.types().keySet()),
                "and that order is the spellings', which is what they are keyed on");
    }

    /** Spellings every claim on which failed, so each stands for nothing and all four answer. */
    private static ResolvedImports imports(String... settledInThisOrder) {
        Map<String, ResolvedImport> settled = new LinkedHashMap<>();
        for (String spelling : settledInThisOrder) {
            settled.put(spelling, new ResolvedImport.BringsNothing(
                    new ResolvedImport.Held(false, false)));
        }
        return new ResolvedImports(settled);
    }
}
