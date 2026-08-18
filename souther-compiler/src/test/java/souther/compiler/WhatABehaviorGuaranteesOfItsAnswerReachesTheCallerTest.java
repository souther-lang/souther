package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a behavior guarantees of its answer is what a caller may assume of it — including where no
 * arm ever opens that answer.
 *
 * <p>A behavior whose output has no cases is never matched, so until here its answer was named by
 * nothing: no subject, and so nothing for either its type's invariant or its {@code ensures} to be
 * written under. A construction downstream of such a call was then not proved, not refuted, and not
 * reported (#819). The silence was the whole of the problem, and silence is also what a check that
 * never ran looks like — so every test here says what the same program is like with the guarantee
 * taken away, and expects the construction to be an unproven one (E2011) there.
 *
 * <p>Both spellings of the same program, because they are the same program. Naming a call and
 * writing it where it is used differ in nothing an author means, and a check that answered them
 * differently would be one where naming a value changes what is known of it.
 */
class WhatABehaviorGuaranteesOfItsAnswerReachesTheCallerTest {

    private static List<Diagnostic> unproven(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    private static final String ENSURES = "    ensures value.rank > id.value\n";

    /** A caseless answer, its behavior stating a relation between what it was given and what it
     * answered. `id.value >= 0` and `rank > id.value` give `rank > 0`, which is `Ranked`'s. */
    private static String statingARelation(String body) {
        return """
                module m.a exposing ( Id, Found, Ranked, findIt, use )

                data Id     = Int
                data Found  = { rank: Int }
                data Ranked = Int
                    invariant value > 0

                behavior findIt : (id: Id) -> Found
                    constructs Found
                """ + ENSURES + """

                let findIt (id) = Found { rank = id.value + 1 }

                behavior use : (id: Id) -> Ranked
                    constructs Ranked
                """ + body;
    }

    private static final String NAMED = """
            let use (id) = {
                guard id.value >= 0
                    else Ranked(1)
                let answer = findIt(id)
                Ranked(answer.rank)
            }
            """;

    private static final String WRITTEN_WHERE_IT_IS_USED = """
            let use (id) = {
                guard id.value >= 0
                    else Ranked(1)
                Ranked(findIt(id).rank)
            }
            """;

    @Test
    void anEnsuresOnAnAnswerNoArmOpensReachesTheCaller() {
        assertEquals(List.of(), unproven(statingARelation(NAMED)),
                "declared of every answer, so it holds of this one");
        assertEquals(1, unproven(statingARelation(NAMED).replace(ENSURES, "")).size(),
                "and with nothing declared it is the unproven construction it always was");
    }

    /** The same, with the call written where its name stood. */
    @Test
    void theSameWhereTheCallIsWrittenWhereItIsUsed() {
        assertEquals(List.of(), unproven(statingARelation(WRITTEN_WHERE_IT_IS_USED)),
                "naming the answer is not what carries the relation");
        assertEquals(1,
                unproven(statingARelation(WRITTEN_WHERE_IT_IS_USED).replace(ENSURES, "")).size(),
                "and taking the relation away leaves this spelling unproven too");
    }

    /**
     * And what the answer's own type states, which needs nothing declared at the behavior.
     *
     * <p>The same value handed in as a parameter carried its type's invariant all along; handed back
     * as an answer it carried nothing, which is the asymmetry underneath #819. An answer is a value
     * of its type built through that type's checked constructor, exactly as a parameter is.
     */
    @Test
    void theInvariantOfTheAnswersOwnTypeReachesTheCaller() {
        String source = """
                module m.e exposing ( Id, Found, Ranked, findIt, use )

                data Id     = Int
                data Found  = { rank: Int }
                    invariant rank > 0
                data Ranked = Int
                    invariant value > 0

                behavior findIt : (id: Id) -> Found
                    constructs Found

                let findIt (id) = Found { rank = 1 }

                behavior use : (id: Id) -> Ranked
                    constructs Ranked
                let use (id) = {
                    let answer = findIt(id)
                    Ranked(answer.rank)
                }
                """;

        assertEquals(List.of(), unproven(source),
                "`Found` guarantees `rank > 0` of every value of it, this one included");
        assertEquals(1, unproven(source.replace("    invariant rank > 0\n", "")).size(),
                "and a `Found` that guarantees nothing leaves the construction unproven");
    }
}
