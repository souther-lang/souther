package souther.compiler.query;

import souther.compiler.check.InliningPolicy;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which recursive helpers a body could hold a standing call to, and which ones this module turned
 * out to reach, are two questions with two answers.
 *
 * <p>A call is left standing because its callee recurses, and which declarations recurse follows
 * from the declarations in reach — the module's own, what its imports publish to it, and the
 * library underneath both. Nothing about any one body decides it. So the names a call here could be
 * written under are those, whether or not this module writes one.
 *
 * <p>What the module reaches is narrower and is a different reader's question: a helper it reaches
 * has to be processed and emitted as a method of its own, and one it does not reach has no body
 * anybody wants. Answering the first question with the second is what left a rule reaching a fold
 * with no signature for the fold it becomes, and answering the second with the first costs a body
 * that does not exist.
 *
 * <p>Held here rather than at either reader, because the whole of the claim is that the two answers
 * differ — a module that reaches nothing still has the library's recursion in the first.
 */
class WhatCanStandUnexpandedIsWiderThanWhatAModuleTookOnTest {

    /** A module that reaches no fold at all, and so takes nothing on. */
    private static final String REACHES_NOTHING = """
            module plain

            data Count = Int

            behavior countIt : (n: Int) -> Count
            let countIt (n) = Count { value = n }
            """;

    /** The same, with a recursion of its own. */
    private static final String ITS_OWN_RECURSION = """
            module owned

            data Emp = { boss: Emp? }
            data Count = Int

            let depth (e: Emp) : Int =
                match e.boss with
                    | Some b -> 1 + depth(b)
                    | None   -> 0

            behavior countIt : (e: Emp) -> Count
            let countIt (e) = Count { value = depth(e) }
            """;

    private static Db dbOf(String module, String source) {
        return Compilation.ofDocuments(Map.of(module + ".sou", source), Set.of(), ModulePath.EMPTY)
                .db();
    }

    private static Map<String, Type> canStand(Db db, String module, InliningPolicy policy) {
        Answer<Map<String, Type>> answer = db.ask(new Bodies.RecursiveCallSigs(module, policy));
        assertTrue(answer.present(), "signatures for " + module + ": " + answer.reports());
        return answer.value();
    }

    /**
     * The library's one recursion is behind every list quantifier, so a call of it can stand in any
     * module of the emitted representation. That this module reaches none is a separate answer, and
     * here it is empty.
     */
    @Test
    void theLibrarysRecursionCanStandInAModuleThatReachesNothing() {
        Db db = dbOf("plain", REACHES_NOTHING);

        assertTrue(canStand(db, "plain", InliningPolicy.FULL).containsKey("List.foldFrom"),
                "what can stand: " + canStand(db, "plain", InliningPolicy.FULL).keySet());
        assertEquals(Set.of(), db.ask(new Bodies.RecursiveHelpers("plain")).value(),
                "and this module took nothing on");
    }

    /**
     * The discharge representation leaves the language's own operations standing rather than
     * expanding them into the fold they become, so its table holds none of the library and the fold
     * is not among the names a call there could be written under.
     */
    @Test
    void andCannotStandInTheRepresentationThatNeverExpandsAQuantifier() {
        Db db = dbOf("plain", REACHES_NOTHING);

        assertFalse(canStand(db, "plain", InliningPolicy.DISCHARGE).containsKey("List.foldFrom"),
                "what can stand: " + canStand(db, "plain", InliningPolicy.DISCHARGE).keySet());
    }

    /** A module's own recursion is in both answers: it can stand, and this module holds its body. */
    @Test
    void aModulesOwnRecursionIsInBothAnswers() {
        Db db = dbOf("owned", ITS_OWN_RECURSION);

        assertTrue(canStand(db, "owned", InliningPolicy.FULL).containsKey("depth"),
                "what can stand: " + canStand(db, "owned", InliningPolicy.FULL).keySet());
        assertTrue(db.ask(new Bodies.RecursiveHelpers("owned")).value().contains("depth"));
    }

    /** And a signature is the declaration's own, not something worked out from the call sites. */
    @Test
    void aSignatureIsTheOneTheDeclarationWasWrittenWith() {
        Type fold = canStand(dbOf("plain", REACHES_NOTHING), "plain", InliningPolicy.FULL)
                .get("List.foldFrom");

        assertTrue(fold instanceof Type.FnOf, "the fold is typed as a function, and was: " + fold);
        assertEquals(4, ((Type.FnOf) fold).params().size(),
                "the step, the seed, the list and the index it walks from");
    }
}
