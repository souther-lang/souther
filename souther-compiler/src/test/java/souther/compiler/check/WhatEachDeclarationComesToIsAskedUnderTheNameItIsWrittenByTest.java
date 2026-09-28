package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an index of a module's declarations answers when it is asked about all of them at once.
 *
 * <p>Three readers wanted the same thing off it: what each declaration comes to, under the name it
 * is written by. Written as a loop at each of them, the walk over the declarations was in the
 * readers' hands, and what settled that none of them read its order was that none of them happened
 * to — which is a fact about those three readers and not about the answer. Asked here, the answer
 * is written under the name the walk hands over, so no turn can overwrite another's.
 *
 * <p>That the walk's order goes nowhere is not held by a case here. Two answers keyed by name
 * compare equal whichever order they were filled in, so no fixture can tell a reading that took an
 * order off this from one that did not: what says it is the census #1760 is counted with, and this
 * says what the operation answers.
 */
class WhatEachDeclarationComesToIsAskedUnderTheNameItIsWrittenByTest {

    /** Every declaration, under its own name, and nothing else. */
    @Test
    void everyDeclarationIsAnsweredUnderItsOwnName() {
        DeclaredNames.Index<String> index = indexOf("a", "b", "c");

        assertEquals(Map.of("a", "a!", "b", "b!", "c", "c!"), index.byName(each -> each + "!"),
                "each declaration is answered under the name it is written by");
        assertEquals(index.declarations().keySet(), index.byName(each -> each).keySet(),
                "and the names answered for are the names declared");
    }

    /** A module that writes the same declarations in another order gets the same answer. */
    @Test
    void theOrderTheDeclarationsWereWrittenInIsNoPartOfTheAnswer() {
        assertEquals(indexOf("a", "b", "c").byName(each -> each + "!"),
                indexOf("c", "b", "a").byName(each -> each + "!"),
                "what each declaration comes to is the same whichever order they were written in");
    }

    /** An index over declarations that are their own names, written in the order given. */
    private static DeclaredNames.Index<String> indexOf(String... written) {
        Map<String, String> declared = new LinkedHashMap<>();
        for (String name : written) {
            declared.put(name, name);
        }
        return new DeclaredNames.Index<>(declared, List.of(written), List.of());
    }
}
