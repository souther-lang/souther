package souther.compiler.reading;

import souther.compiler.Compiler;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm written for several cases is the condition that the value is one of them.
 *
 * <p>A set of cases, and read as one wherever two conditions meet: two sets that share a case can
 * both hold, since the value can be that case, and only two with none in common are one decision
 * settled two ways. The order the cases were written in is nothing the condition is.
 */
class AnArmForSeveralCasesIsASetOfThemTest {

    private static final TermPath K = TermPath.of("k");

    @Test
    void twoArmsNamingTheSameCasesInAnotherOrderAreOneCondition() {
        assertEquals(new Condition.Case(K, List.of("A", "B")),
                new Condition.Case(K, List.of("B", "A")));
    }

    @Test
    void setsThatShareACaseDoNotExcludeEachOther() {
        Condition.Case ab = new Condition.Case(K, List.of("A", "B"));

        assertFalse(ab.excludes(new Condition.Case(K, List.of("A"))), "the value can be A");
        assertFalse(ab.excludes(new Condition.Case(K, List.of("B", "C"))), "the value can be B");
        assertTrue(ab.excludes(new Condition.Case(K, List.of("C"))), "no case is in both");
        assertFalse(ab.excludes(new Condition.Case(TermPath.of("j"), List.of("C"))),
                "two positions are two decisions");
    }

    /**
     * An arm under one for several cases is reached for each case it shares with it.
     *
     * <p>The inner match is on the value the outer arm admits as {@code A} or {@code B}. Its arms for
     * those two are ways a run takes; the one for {@code C} is the only arm no run reaches.
     */
    @Test
    void anArmInsideAnArmForSeveralCasesIsReachedByEachCaseTheyShare() {
        Compilation compilation = Compiler.analyzedModules(List.of("""
                module example.nested

                data A
                data B
                data C
                data Kind = A | B | C

                data Ok = { n: Int }

                behavior judge : (k: Kind) -> Ok
                    constructs Ok

                let judge (k) =
                    match k with
                        | A | B ->
                            match k with
                                | A -> Ok { n = 1 }
                                | B -> Ok { n = 2 }
                                | C -> Ok { n = 3 }
                        | C -> Ok { n = 4 }

                example judge
                    | (A) -> Ok { n = 1 }
                """), ModulePath.EMPTY, new ArrayList<>(), Adequacy.Asked.fullReport());
        CoverageRead.Read read = compilation.db()
                .ask(new Adequacy.Meets("example.nested")).value().get("judge");

        long unreachable = read.arms().values().stream()
                .filter(each -> each instanceof PathAccess.Unreachable).count();
        assertEquals(1, unreachable,
                () -> "only the inner arm for C is out of reach: " + read.arms());
    }

    /**
     * And past an attempted construction as well, where no way in is named.
     *
     * <p>Which way the attempt goes rules out nothing about {@code k}, which is an input and the same
     * value wherever the run gets to. So what the outer arm let through holds past it, and an inner
     * arm for a case outside that is one no run reaches — a proof, and not a way this reading could
     * not name.
     */
    @Test
    void anArmPastAnAttemptThatTheWayToItRulesOutIsReachedByNoRun() {
        Compilation compilation = Compiler.analyzedModules(List.of("""
                module example.pastattempt

                data A
                data B
                data C
                data Kind = A | B | C

                data Note = String
                    invariant String.length(value) >= 1
                data NoNote

                data Ok = { n: Int }

                behavior judge : (k: Kind, text: String) -> Ok | NoNote
                    constructs Ok, Note

                let judge (k, text) =
                    match k with
                        | A | B -> {
                            guard Note(text) as note else NoNote
                            match k with
                                | A -> Ok { n = 1 }
                                | B -> Ok { n = 2 }
                                | C -> Ok { n = 3 }
                        }
                        | C -> Ok { n = 4 }

                example judge
                    | (A, "a") -> Ok { n = 1 }
                """), ModulePath.EMPTY, new ArrayList<>(), Adequacy.Asked.fullReport());
        CoverageRead.Read read = compilation.db()
                .ask(new Adequacy.Meets("example.pastattempt")).value().get("judge");

        long unreachable = read.arms().values().stream()
                .filter(each -> each instanceof PathAccess.Unreachable).count();
        assertEquals(1, unreachable,
                () -> "the inner arm for C is reached by no run: " + read.arms());
    }
}
