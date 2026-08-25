package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.check.BehaviorContract;
import souther.compiler.check.CheckedEnsures;
import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior declares about its answer is a thing somebody holds.
 *
 * <p>It was read for its diagnostics and thrown away: the check called for it, kept whatever it
 * refused, and let the contract go. Every reader that wanted it afterwards — the emitter, the
 * classification, the editor, the analysis at a call — would have worked it out again from the
 * declaration, and each of those would have been a second answer to what a case means and what the
 * parameters are called.
 *
 * <p>The reports come with it. Reading a clause is what finds a clause that cannot be read, so a
 * caller cannot take the contracts and leave the refusals behind — which is what made the old shape
 * work by accident: the diagnostics existed because the type check happened to ask first.
 */
class AContractIsOwnedWithWhatReadingItFoundTest {

    private static final String HOLDS = """
            module m.a exposing ( Id, Found, Missing, findIt )

            data Id      = Int
            data Found   = { id: Id }
            data Missing = { asked: Id }

            behavior findIt : (id: Id) -> Found | Missing
                constructs Found, Missing
                ensures answersTheRequest = Found   -> value.id == id
                                          | Missing -> value.asked == id

            let findIt (id) = if id.value > 0 then Found { id = id } else Missing { asked = id }
            """;

    private static Compilation compiled(String source) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", source);
        return Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
    }

    private static Answer<Map<String, CheckedEnsures>> contracts(String source) {
        return compiled(source).db().ask(new Bodies.Contracts("m.a"));
    }

    @Test
    void theContractIsTheAnswerAndNotASideEffect() {
        Answer<Map<String, CheckedEnsures>> answered = contracts(HOLDS);

        assertTrue(answered.present(), "a module whose clauses read has contracts to hand over");
        assertFalse(answered.hasError(), "and nothing to report about them");

        BehaviorContract contract = answered.value().get("findIt").read();
        assertEquals(2, contract.rules().size(),
                "one rule per case an arm names — the specialization is done once, here");
        assertEquals(1, contract.params().size(), "and the parameters a rule names come with it");
    }

    /** A behavior stating nothing is absent rather than empty: absence is the answer to "is there a
     *  check to emit", and an empty contract would be a second way to say it. */
    @Test
    void aBehaviorThatDeclaresNothingIsNotThere() {
        Answer<Map<String, CheckedEnsures>> answered = contracts("""
                module m.a exposing ( Id, echo )

                data Id = Int

                behavior echo : (id: Id) -> Id
                let echo (id) = id
                """);

        assertTrue(answered.present());
        assertEquals(Map.of(), answered.value());
    }

    /**
     * The refusal rides the same answer.
     *
     * <p>`value` alone states a property of the answer, which belongs on its type — so this is
     * refused, and the refusal is what asking for the contracts hands back. Nothing else has to have
     * run for it to be there.
     */
    @Test
    void aClauseThatCannotBeReadIsReportedByTheKeyThatReadsIt() {
        Answer<Map<String, CheckedEnsures>> answered = contracts(HOLDS
                .replace("Found   -> value.id == id", "Found   -> value.id == value.id"));

        assertTrue(answered.hasError(),
                "the reading found it, so the reading is what carries it");
        assertTrue(answered.reports().stream()
                        .anyMatch(r -> r.diagnostic().code().equals("E1617")),
                "a rule naming no parameter: " + answered.reports());
    }

    /**
     * And the refusal still stops a build.
     *
     * <p>The reading used to sit inside the type check, so a build was refused because the check
     * happened to walk the clause. Now the clause has a key of its own, and what makes a build stop
     * is that the key is asked and its reports are read — asserted here rather than left to the fact
     * that some other reader currently asks first.
     */
    @Test
    void aRefusedClauseStopsTheBuild() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(HOLDS
                .replace("Found   -> value.id == id", "Found   -> value.id == value.id")));

        assertEquals("E1617", e.diagnostic().code());
    }
}
