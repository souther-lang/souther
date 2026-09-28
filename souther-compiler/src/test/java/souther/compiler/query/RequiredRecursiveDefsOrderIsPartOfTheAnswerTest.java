package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@code Bodies.RequiredRecursiveDefs}'s own {@code compute} says the order of a mutual cycle's
 * members is part of the answer, so an edit that swaps which one was declared first has to be seen
 * as a changed answer — not just a changed set. That rests on the answer's type: a {@link List}'s
 * {@code equals} reads order, a {@code Set}'s (what this answer used to be) does not — which is what
 * let {@code Db.ask}'s {@code memo.answer().equals(answer)} call miss a reorder entirely (issue
 * #1835, the same defect #1833 fixed for {@code RowWork.arms}).
 */
class RequiredRecursiveDefsOrderIsPartOfTheAnswerTest {

    private static final String PING_FIRST = """
            module demo

            data N = Int
            data Steps = Int

            behavior countHops : (n: N) -> Steps constructs Steps

            partial let ping (n: Int): Int = if n == 0 then 0 else pong(n - 1) + 1
            partial let pong (n: Int): Int = if n == 0 then 0 else ping(n - 1) + 1

            let countHops (n) = Steps(ping(n.value))
            """;

    private static final String PONG_FIRST = """
            module demo

            data N = Int
            data Steps = Int

            behavior countHops : (n: N) -> Steps constructs Steps

            partial let pong (n: Int): Int = if n == 0 then 0 else ping(n - 1) + 1
            partial let ping (n: Int): Int = if n == 0 then 0 else pong(n - 1) + 1

            let countHops (n) = Steps(ping(n.value))
            """;

    private static Compilation started(String source) {
        Compilation c = Compilation.ofDocuments(Map.of("demo.sou", source), Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");
        return c;
    }

    private static List<String> rendered(List<souther.compiler.types.ReachName.Declaration> answer) {
        return answer.stream().map(souther.compiler.types.ReachName.Declaration::rendered).toList();
    }

    @Test
    void swappingWhichMemberOfTheCycleWasDeclaredFirstChangesTheAnswer() {
        Compilation c = started(PING_FIRST);
        Answer<List<souther.compiler.types.ReachName.Declaration>> before =
                c.db().ask(new Bodies.RequiredRecursiveDefs("demo"));
        assertEquals(List.of("ping", "pong"), rendered(before.value()));

        c.update(Map.of("demo.sou", PONG_FIRST), Set.of());
        c.answerEverything();
        Answer<List<souther.compiler.types.ReachName.Declaration>> after =
                c.db().ask(new Bodies.RequiredRecursiveDefs("demo"));

        assertEquals(List.of("pong", "ping"), rendered(after.value()));
        assertNotEquals(before.value(), after.value(),
                "same two declarations, different order: a List sees that as a different answer,"
                        + " which is what makes the reorder visible to Db's changedAt — a"
                        + " SequencedSet's equals would have called these the same");
    }

    /**
     * {@code Bodies.Expanding} — the dependency {@code RequiredRecursiveDefs} and
     * {@code RecursiveCallSigs} both read the cycle's order off — has to see the same reorder in its
     * own answer's {@code equals}, or a reader with no other order-sensitive dependency (unlike
     * {@code RequiredRecursiveDefs}, which also reads {@code Settled} directly) would keep serving a
     * build made against the cycle's old order. {@code HelperGraph.recursive} being a {@link List}
     * and {@code HelperTable}'s own {@code equals} reading {@code reachable()}'s order are both
     * needed for this: {@code HelperGraph} is a record, so a {@code List} component alone fixes its
     * generated {@code equals}, but {@code HelperTable.byReference} is a plain field a record-style
     * {@code equals} would still compare with {@code Map.equals}.
     */
    @Test
    void expandingItselfSeesTheReorderNotOnlyRequiredRecursiveDefs() {
        Compilation c = started(PING_FIRST);
        Answer<Bodies.Expanding.Of> before = c.db().ask(
                new Bodies.Expanding("demo", souther.compiler.check.InliningPolicy.FULL));
        assertEquals(List.of("List.foldFrom", "ping", "pong"),
                rendered(before.value().graph().recursive()));

        c.update(Map.of("demo.sou", PONG_FIRST), Set.of());
        c.answerEverything();
        Answer<Bodies.Expanding.Of> after = c.db().ask(
                new Bodies.Expanding("demo", souther.compiler.check.InliningPolicy.FULL));

        assertEquals(List.of("List.foldFrom", "pong", "ping"),
                rendered(after.value().graph().recursive()));
        assertNotEquals(before.value(), after.value(),
                "Expanding.Of wraps HelperTable and HelperGraph, both of which now carry order as"
                        + " part of what they mean — this must not go stale under equals just"
                        + " because it is nested a level below RequiredRecursiveDefs");
    }
}
