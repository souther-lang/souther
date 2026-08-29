package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;
import souther.compiler.jvm.ClassFileImage;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a behavior declared about its answer is what a caller that reached the case may assume.
 *
 * <p>This is what an {@code ensures} is for, and until here it was a run-time check and nothing
 * else. A relation between what a behavior was given and what it answered fits on neither type — the
 * answer does not hold the input — so a caller had to establish it again with a {@code guard} it
 * could not derive, and the declaration cost something and paid nothing.
 *
 * <p>Measured by a construction downstream of the call: the seeding either carries the relation to
 * it, in which case nothing is reported, or it does not, in which case the construction is an
 * unproven one (E2011). Every test that asserts silence says what the same program is like with the
 * clause taken away, because silence on its own is what a check that never ran also looks like.
 */
class ACallerMayAssumeWhatTheAnswerWasDeclaredToBeTest {

    private static final String CLAUSE = "    ensures Found -> value.rank > id.value\n";

    private static final String DECLARES = """
            module m.a exposing ( Id, Found, Missing, Ranked, findIt, use )

            data Id      = Int
            data Found   = { rank: Int }
            data Missing = { asked: Id }
            data Ranked  = Int
                invariant value > 0

            behavior findIt : (id: Id) -> Found | Missing
                constructs Found, Missing
            """ + CLAUSE + """

            let findIt (id) =
                if id.value > 0 then Found { rank = id.value } else Missing { asked = id }

            behavior use : (id: Id) -> Ranked | Missing
                constructs Ranked, Missing
            """;

    private static final String THROUGH_A_MATCH = """
            let use (id) = {
                guard id.value >= 0
                    else Missing { asked = id }
                match findIt(id) with
                    | Found as found -> Ranked(found.rank)
                    | Missing as missing -> missing
            }
            """;

    private static List<Diagnostic> unproven(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    private static String withoutTheClause(String source) {
        return source.replace(CLAUSE, "");
    }

    @Test
    void aRelationDeclaredOnTheAnswerReachesAConstructionAfterTheMatch() {
        // `value.rank > id.value` and the guard `id.value >= 0` give `rank > 0`, which is `Ranked`'s
        assertEquals(List.of(), unproven(DECLARES + THROUGH_A_MATCH),
                "declared, matched, assumed — so the construction is settled");
        assertEquals(1, unproven(withoutTheClause(DECLARES + THROUGH_A_MATCH)).size(),
                "and with nothing declared it is the unproven construction it always was");
    }

    /**
     * The call is reached through the name it was given.
     *
     * <p>{@code let r = findIt(id)} and {@code match findIt(id)} are one program to an author. A
     * reader asking whether the scrutinee <em>is</em> a call answers only the second, and the first
     * is how anybody writes it who wants to name the answer.
     */
    @Test
    void theCallIsFollowedThroughTheNameItWasGiven() {
        String throughALet = """
                let use (id) = {
                    guard id.value >= 0
                        else Missing { asked = id }
                    let answer = findIt(id)
                    match answer with
                        | Found as found -> Ranked(found.rank)
                        | Missing as missing -> missing
                }
                """;

        assertEquals(List.of(), unproven(DECLARES + throughALet));
        assertEquals(1, unproven(withoutTheClause(DECLARES + throughALet)).size());
    }

    /**
     * An arm answering for several cases says the answer is one of them, which is not that it is any
     * one of them. A rule about {@code Found} is a rule about a value this arm may not have.
     */
    @Test
    void anArmAnsweringForSeveralCasesAssumesNothingAboutOneOfThem() {
        String orPattern = """
                let use (id) = {
                    guard id.value >= 0
                        else Missing { asked = id }
                    match findIt(id) with
                        | Found | Missing as either -> Ranked(id.value)
                }
                """;

        assertEquals(1, unproven(DECLARES + orPattern).size(),
                "`Found`'s rule says nothing here, so this construction is as unproven as ever");
    }

    /**
     * A rule with a part this cannot read still says the part it can.
     *
     * <p>The unit is the conjunct everywhere else a clause is read, and dropping a rule for the half
     * that got away would leave a caller with less than the declaration gives them.
     */
    @Test
    void aRuleHalfOfWhichCannotBeReadStillSaysTheOtherHalf() {
        String source = """
                module m.b exposing ( Id, Found, Ranked, findIt, use )

                data Id     = Int
                data Found  = { rank: Int, tag: String }
                data Ranked = Int
                    invariant value > 0

                behavior findIt : (id: Id) -> Found
                    constructs Found
                    ensures String.startsWith(value.tag, "x") && value.rank > id.value

                let findIt (id) = Found { rank = id.value + 1, tag = "x" }

                behavior use : (id: Id) -> Ranked
                    constructs Ranked
                let use (id) = {
                    guard id.value >= 0
                        else Ranked(1)
                    let answer = findIt(id)
                    Ranked(answer.rank)
                }
                """;

        assertEquals(List.of(), unproven(source),
                "`value.rank > id.value` was read, whatever became of the half beside it");
        // The control cannot be the rule taken away. Say nothing about an answer and there is
        // nothing for a clause about it to be discharged from, so the construction is one the
        // run-time check stands for and this is silent either way. A rule that refutes it is the
        // control that works: it can only refuse by having reached the construction, which is what
        // the silence above needs saying about it.
        assertThrows(souther.compiler.diag.CompileException.class,
                () -> unproven(source.replace("value.rank > id.value",
                        "value.rank + id.value < 0")),
                "a rule that refutes the construction refuses it, so the rule reached it");
    }


    /**
     * What another module declared is what a caller in this one may assume.
     *
     * <p>The relation belongs to the behavior, so it is read from the module that declares it —
     * which is where an author reading the call would look for it, and the only place it is written.
     */
    @Test
    void aRelationDeclaredInAnotherModuleReachesItsCallerHere() {
        String declaring = """
                module up exposing ( Id, Found, Missing, findIt )

                data Id      = Int
                data Found   = { rank: Int }
                data Missing = { asked: Id }

                behavior findIt : (id: Id) -> Found | Missing
                    constructs Found, Missing
                    ensures Found -> value.rank > id.value

                let findIt (id) =
                    if id.value > 0 then Found { rank = id.value } else Missing { asked = id }
                """;
        String calling = """
                module down exposing ( Ranked, use )

                import up ( Id, Found, Missing, findIt )

                data Ranked = Int
                    invariant value > 0

                behavior use : (id: Id) -> Ranked | Missing
                    constructs Ranked, Missing
                let use (id) = {
                    guard id.value >= 0
                        else Missing { asked = id }
                    match findIt(id) with
                        | Found as found -> Ranked(found.rank)
                        | Missing as missing -> missing
                }
                """;

        assertEquals(List.of(), unprovenAcross(List.of(declaring, calling)));
        assertEquals(1, unprovenAcross(List.of(
                declaring.replace("    ensures Found -> value.rank > id.value\n", ""),
                calling)).size(),
                "and with nothing declared up there, the construction down here is unproven");
    }

    private static List<Diagnostic> unprovenAcross(List<String> sources) {
        return Compiler.compileModulesWithWarnings(sources).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    /**
     * And what the module published, not only what this compile happened to hold.
     *
     * <p>A module reached through its classes is a different path to the same question: what its
     * author wrote travels as the declaration it published and is read back by this front end
     * (ADR-0063), and nothing of the module that declared it is compiled here. A caller assuming a
     * relation is a language guarantee across that boundary or it is a guarantee only inside one
     * build.
     */
    @Test
    void aRelationPublishedByAnotherProjectReachesItsCallerHere() {
        String library = """
                module shared.finding exposing ( Id, Found, Missing, findIt )

                data Id      = Int
                data Found   = { rank: Int }
                data Missing = { asked: Id }

                behavior findIt : (id: Id) -> Found | Missing
                    constructs Found, Missing
                    ensures Found -> value.rank > id.value

                let findIt (id) =
                    if id.value > 0 then Found { rank = id.value } else Missing { asked = id }
                """;
        String consumer = """
                module app.ranking exposing ( Ranked, use )

                import shared.finding ( Id, Found, Missing, findIt )

                data Ranked = Int
                    invariant value > 0

                behavior use : (id: Id) -> Ranked | Missing
                    constructs Ranked, Missing
                let use (id) = {
                    guard id.value >= 0
                        else Missing { asked = id }
                    match findIt(id) with
                        | Found as found -> Ranked(found.rank)
                        | Missing as missing -> missing
                }
                """;

        assertEquals(List.of(), unprovenAgainst(consumer, library),
                "the relation was read back off the published declaration and assumed here");
        assertEquals(1, unprovenAgainst(consumer,
                        library.replace("    ensures Found -> value.rank > id.value\n", "")).size(),
                "and a library that declares nothing leaves the construction unproven, as before");
    }

    /** The consumer compiled on its own, against the library's classes and none of its source. */
    private static List<Diagnostic> unprovenAgainst(String consumer, String library) {
        Map<String, ClassFileImage> classes = Compiler.compile(library);
        return Compiler.compileModulesWithWarnings(List.of(consumer), ModulePath.of(classes))
                .warnings()
                .stream().filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }
}
