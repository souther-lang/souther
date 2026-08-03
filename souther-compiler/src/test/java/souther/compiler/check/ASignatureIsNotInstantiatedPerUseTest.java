package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Where a library signature's type variables come from, and what happens to the ones a call leaves
 * unsolved. Read before deciding where a helper's own variables have to be minted.
 *
 * <p>A signature is resolved once, when the library is loaded, and every call site reads that one
 * value. Nothing instantiates it: a call builds its own bindings map and substitutes, so a variable
 * the call solves becomes what it was solved to, and one it does not solve comes back out as the
 * variable the library wrote. Two unrelated calls therefore hand back the same {@code 'a}.
 */
class ASignatureIsNotInstantiatedPerUseTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    /** Two library functions that both wrote {@code 'a} hand back one name for two unrelated
     * elements — which is what a helper's own minting has to separate. */
    @Test
    void twoLibrarySignaturesSpellTheirVariableTheSame() {
        Type fromList = Prelude.entry("List.length").signature().params().get(0);
        Type fromSet = Prelude.entry("Set.size").signature().params().get(0);
        assertEquals(Type.list(Type.var("'a")), fromList);
        assertEquals(Type.set(Type.var("'a")), fromSet);
    }

    /**
     * A variable the position already settled is solved to what the position said, so a name that
     * came in from the expected type is carried out rather than replaced. This is the path a second
     * parameter takes when the first one is already in force: {@code List.get}'s result is asked for
     * {@code Option<$0>}, and its parameter comes back as {@code List<$0>}.
     */
    @Test
    void aVariableTheExpectedTypeSettledComesBackAsThatType() {
        Prelude.Signature get = Prelude.entry("List.get").signature();
        Map<String, Type> bind = new HashMap<>();
        BottomInfer.pinResultTypeVars(get.result(), Type.option(Type.var("$0")), bind,
                null, POS, "result");
        assertEquals(Type.var("$0"), bind.get("'a"));
        assertEquals(Type.list(Type.var("$0")), TypeOps.substitute(get.params().get(1), bind));
    }
}
