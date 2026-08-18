package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a behavior guarantees of its answer is what a caller may assume of it — including where no
 * arm ever opens that answer.
 *
 * <p>A behavior whose output has no cases is never matched, so until here its answer was named by
 * nothing: no subject, and so nothing for either its type's invariant or its {@code ensures} to be
 * written under. A construction downstream of such a call was then not proved, not refuted, and not
 * reported (#819). The silence was the whole of the problem, and silence is also what a check that
 * never ran looks like, so nothing here rests on it alone.
 *
 * <p>Both spellings of the same program, because they are the same program. Naming a call and
 * writing it where it is used differ in nothing an author means, and a check that answered them
 * differently would be one where naming a value changes what is known of it.
 *
 * <p>The control is never the guarantee taken away. Declare nothing about an answer and there is
 * nothing for a clause about it to be discharged from, so the construction is one the run-time check
 * stands for and the compile is silent — correctly, and as it was before any of this. Silence is
 * therefore the wrong control for silence. A guarantee that <em>refutes</em> the construction is the
 * right one: it can only refuse by having reached it.
 */
class WhatABehaviorGuaranteesOfItsAnswerReachesTheCallerTest {

    private static List<Diagnostic> unproven(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    /**
     * The code the compile refused this source with, or {@code null} where it compiled.
     *
     * <p>The control every test here needs, and it cannot be the guarantee taken away. Say nothing
     * about an answer and there is nothing to read a clause against, so the construction is one the
     * run-time check stands for and the compile is silent — which is what it was before any of this,
     * and is correct: an answer having an identity is not a reason to start reporting on it. Silence
     * is therefore the wrong control for silence. A guarantee that <em>refutes</em> the construction
     * is the right one: it can only be refuted if the rule reached, so the refusal is the evidence
     * the passing case cannot give on its own.
     */
    private static String refusedWith(String source) {
        try {
            Compiler.compileWithWarnings(source);
            return null;
        } catch (souther.compiler.diag.CompileException refused) {
            String said = refused.getMessage();
            int at = said.indexOf("E2");
            return at < 0 ? said : said.substring(at, at + 5);
        }
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
        assertEquals("E2010", refusedWith(statingARelation(NAMED)
                        .replace(ENSURES, "    ensures value.rank + id.value < 0\n")),
                "and a relation that refutes the construction refuses it, which it can only do "
                        + "by having reached it");
    }

    /** The same, with the call written where its name stood. */
    @Test
    void theSameWhereTheCallIsWrittenWhereItIsUsed() {
        assertEquals(List.of(), unproven(statingARelation(WRITTEN_WHERE_IT_IS_USED)),
                "naming the answer is not what carries the relation");
        assertEquals("E2010", refusedWith(statingARelation(WRITTEN_WHERE_IT_IS_USED)
                        .replace(ENSURES, "    ensures value.rank + id.value < 0\n")),
                "and this spelling is refused by a refuting relation just the same");
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
        assertEquals("E2010", refusedWith(source.replace("    invariant rank > 0\n",
                        "    invariant rank < 0\n")),
                "and a `Found` whose invariant refutes the construction refuses it");
    }

    /**
     * What an answer guarantees is taken in where that answer is reached, and not in the branch
     * beside it.
     *
     * <p>Standing in the subtree is not standing where the walk is. A guarantee relates the answer to
     * the arguments it was given, so taken in from an arm this path never evaluates it lands on the
     * very values the condition is about — one arm's answer then contradicts the other arm's
     * condition, that arm comes out reaching nothing, and its constructions are never judged. The
     * loss is silent, which is the failure this whole issue is about, so it is held here.
     *
     * <p>Read as the count and not as one report: the construction in the {@code then} arm is
     * unproven whatever the {@code else} arm calls, and the two arms answer for themselves.
     */
    @Test
    void whatAnAnswerGuaranteesDoesNotReachTheBranchBesideIt() {
        String source = """
                module m.b exposing ( Id, Found, Ranked, findIt, use )

                data Id     = Int
                data Found  = { rank: Int }
                    invariant rank <= 0
                data Ranked = Int
                    invariant value > 0

                behavior findIt : (id: Id) -> Found
                    constructs Found
                    ensures value.rank > id.value

                let findIt (id) = Found { rank = 0 - id.value - 1 }

                behavior use : (id: Id) -> Ranked
                    constructs Ranked
                let use (id) =
                    if id.value >= 0 then
                        Ranked(id.value)
                    else
                        Ranked(0 - findIt(id).rank)
                """;

        assertEquals(unproven(source.replace("    ensures value.rank > id.value\n", "")).size(),
                unproven(source).size(),
                "the `else` arm's answer says nothing about the `then` arm, so the same "
                        + "constructions are unproven either way");
    }

    /**
     * A value a clause does not actually rest on does not stop the clause being asked about.
     *
     * <p>Whether the author can be asked to account for a construction is decided from the values the
     * clause depends on. An opaque value that appears on both sides of the relation is not one of
     * them — it cancels, and what is left is arithmetic the check could read all along. Asked of the
     * two sides separately instead of the relation between them, this clause would be turned away
     * for a value it does not mention, and a construction the invariant plainly rejects would compile
     * in silence.
     */
    @Test
    void aValueThatCancelsOutOfAClauseDoesNotSilenceIt() {
        String source = """
                module m.c exposing ( Id, Rising, opaque, use )

                data Id     = Int
                data Rising = { a: Int, b: Int }
                    invariant a > b

                behavior opaque : (id: Id) -> Int

                behavior use : (id: Id) -> Rising
                    constructs Rising
                    depends on opaque
                let use (id, opaque) = {
                    let n = opaque(id)
                    Rising { a = n, b = n + 1 }
                }
                """;

        assertThrows(souther.compiler.diag.CompileException.class, () -> unproven(source),
                "`n` cancels and `a - b` is -1, which the invariant rejects however opaque `n` is");
    }

    /**
     * A guarantee that is a predicate reaches the caller too, and not only one that is a number.
     *
     * <p>The half that closing identity for the numeric domain alone would have left behind. A
     * relation between numbers reaches a caller through the affine reading, which composes over
     * whatever atom the answer is; a predicate reaches it through the key a fact is filed under, and
     * that key was still being built the symbolic way — which runs out at an answer exactly as it did
     * before any of this. So {@code ensures value.rank > 0} would arrive and {@code ensures value.ok}
     * would not, which is one guarantee kept and one quietly dropped for no reason an author could
     * see.
     *
     * <p>Read through the refutation, for the reason every control here is: with nothing declared the
     * construction is silent, so silence proves nothing on its own. A guarantee that contradicts the
     * invariant can only refuse by having reached it.
     */
    @Test
    void aGuaranteeThatIsAPredicateReachesTheCallerAsWell() {
        String source = """
                module m.d exposing ( Id, Found, Checked, findIt, use )

                data Id      = Int
                data Found   = { ok: Bool }
                data Checked = { ok: Bool }
                    invariant ok

                behavior findIt : (id: Id) -> Found
                    constructs Found
                    ensures id.value > 0 && value.ok

                let findIt (id) = Found { ok = id.value > 0 }

                behavior use : (id: Id) -> Checked
                    constructs Checked
                let use (id) = {
                    let answer = findIt(id)
                    Checked { ok = answer.ok }
                }
                """;

        assertEquals(List.of(), unproven(source), "`value.ok` holds of the answer, so this is built");
        assertThrows(souther.compiler.diag.CompileException.class,
                () -> unproven(source.replace("&& value.ok", "&& Bool.not(value.ok)")),
                "and a predicate that contradicts the invariant refuses the construction, which it "
                        + "can only do by having reached it");
    }
}
