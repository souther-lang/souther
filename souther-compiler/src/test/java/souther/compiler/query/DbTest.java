package souther.compiler.query;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The query engine on its own: what it memoises, what it records, and what it does when a question
 * turns out to depend on itself. Nothing here knows about Souther — the keys are toys, so what is
 * being tested is the engine and not a pass that happens to run on it.
 */
class DbTest {

    /** How often each key's {@code compute} ran. A key is a value, so it cannot hold the counter
     * itself; the count lives here and the keys reach it as the enclosing class's state. */
    private static final Map<String, Integer> RUNS = new HashMap<>();

    private static void ran(String name) {
        RUNS.merge(name, 1, Integer::sum);
    }

    private static int runs(String name) {
        return RUNS.getOrDefault(name, 0);
    }

    @BeforeEach
    void clearCounts() {
        RUNS.clear();
    }

    /** The text of a file: given from outside, never computed. */
    record Text(String file) implements Input<String> {}

    /** That text in upper case — one computed key reading one input. */
    record Shouted(String file) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("shouted:" + file);
            Answer<String> text = db.ask(new Text(file));
            if (!text.present()) {
                return Answer.absent();
            }
            return Answer.of(text.value().toUpperCase());
        }
    }

    /** Two shouted files joined, so a key with more than one dependency can be observed. */
    record Both(String left, String right) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("both");
            return Answer.of(db.ask(new Shouted(left)).value() + db.ask(new Shouted(right)).value());
        }
    }

    /** A key that reports rather than answers. */
    record Complains(String about) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("complains");
            return Answer.absent(Report.of(Diagnostic.literal(null, "E9999", about)));
        }
    }

    @Test
    void answersAKey() {
        Db db = new Db().set(new Text("a.sou"), "module a");
        assertEquals("MODULE A", db.ask(new Shouted("a.sou")).value());
    }

    @Test
    void computesEachKeyOnce() {
        Db db = new Db().set(new Text("a.sou"), "module a");
        db.ask(new Shouted("a.sou"));
        db.ask(new Shouted("a.sou"));
        assertEquals(1, runs("shouted:a.sou"));
    }

    @Test
    void sharesOneComputationBetweenTwoAskers() {
        Db db = new Db().set(new Text("a.sou"), "x").set(new Text("b.sou"), "y");
        db.ask(new Both("a.sou", "b.sou"));
        db.ask(new Shouted("a.sou"));
        assertEquals(1, runs("shouted:a.sou"));
    }

    @Test
    void recordsWhatAKeyRead() {
        Db db = new Db().set(new Text("a.sou"), "x").set(new Text("b.sou"), "y");
        db.ask(new Both("a.sou", "b.sou"));
        assertEquals(Set.of(new Shouted("a.sou"), new Shouted("b.sou")),
                db.dependenciesOf(new Both("a.sou", "b.sou")));
        assertEquals(Set.of(new Text("a.sou")), db.dependenciesOf(new Shouted("a.sou")));
    }

    @Test
    void reportsTravelWithTheAnswer() {
        Db db = new Db();
        Answer<String> answer = db.ask(new Complains("nope"));
        assertNull(answer.value());
        assertFalse(answer.present());
        assertTrue(answer.hasError());
        assertEquals(1, answer.reports().size());
        assertEquals("nope", answer.reports().get(0).diagnostic().literalMessage());
    }

    @Test
    void raisesTheMessageAPassRaisedItWith() {
        Diagnostic d = Diagnostic.of("E1234", "check.module.duplicate").build();
        CompileException raised = CompileException.of(d, "duplicate module `a`");
        List<Report> reports = Report.of(raised);
        assertEquals(raised.getMessage(), reports.get(0).asException().getMessage());
    }

    @Test
    void memoisesAnAbsentAnswerToo() {
        Db db = new Db();
        db.ask(new Complains("nope"));
        db.ask(new Complains("nope"));
        assertEquals(1, runs("complains"));
    }

    @Test
    void anInputWithNoValueIsAbsentRatherThanAnError() {
        Db db = new Db();
        assertFalse(db.ask(new Text("missing.sou")).present());
        assertFalse(db.ask(new Shouted("missing.sou")).present());
    }

    /** A key that reads itself through another, with an answer for the case. */
    record Ping(int depth) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("ping" + depth);
            return Answer.of("ping" + depth + "-" + db.ask(new Ping(1 - depth)).value());
        }

        @Override
        public Answer<String> onCycle(List<Key<?>> cycle) {
            return Answer.of("cycle" + cycle.size());
        }
    }

    /** A key that reads itself and has nothing to say about it. */
    record Loop() implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            return db.ask(new Loop());
        }
    }

    @Test
    void aCycleGetsTheReenteredKeysOwnAnswer() {
        Db db = new Db();
        // Ping(0) reads Ping(1), which reads Ping(0) again: the second reading is the cycle, and
        // both keys are on the stack when it is found.
        assertEquals("ping0-ping1-cycle2", db.ask(new Ping(0)).value());
    }

    @Test
    void memoisesNothingOnACycle() {
        Db db = new Db();
        db.ask(new Ping(0));
        db.ask(new Ping(0));
        // A cyclic answer depends on where the cycle was entered, so keeping it would make a later
        // asker's answer depend on who asked first.
        assertEquals(2, runs("ping0"));
        assertFalse(db.isComputed(new Ping(0)));
        assertFalse(db.isComputed(new Ping(1)));
    }

    @Test
    void aCycleWithNoAnswerIsAProgrammingError() {
        Db db = new Db();
        assertThrows(IllegalStateException.class, () -> db.ask(new Loop()));
    }

    /** Two files joined, so an edit to one can be watched for its effect on the other. */
    record Length(String file) implements Key<Integer> {
        @Override
        public Answer<Integer> compute(Db db) {
            ran("length:" + file);
            Answer<String> text = db.ask(new Text(file));
            return text.present() ? Answer.of(text.value().length()) : Answer.absent();
        }
    }

    record Longest(String left, String right) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("longest");
            int a = db.ask(new Length(left)).value();
            int b = db.ask(new Length(right)).value();
            return Answer.of(a >= b ? left : right);
        }
    }

    @Test
    void recomputesWhatAnEditCanHaveChanged() {
        Db db = new Db().set(new Text("a.sou"), "one").set(new Text("b.sou"), "two");
        assertEquals(3, db.ask(new Length("a.sou")).value());
        db.set(new Text("a.sou"), "seven!");
        assertEquals(6, db.ask(new Length("a.sou")).value());
        assertEquals(2, runs("length:a.sou"));
    }

    @Test
    void leavesAloneWhatTheEditCannotReach() {
        Db db = new Db().set(new Text("a.sou"), "one").set(new Text("b.sou"), "two");
        db.ask(new Length("b.sou"));
        db.set(new Text("a.sou"), "changed");
        db.ask(new Length("b.sou"));
        assertEquals(1, runs("length:b.sou"));
    }

    @Test
    void stopsWhereTheAnswerCameOutTheSame() {
        Db db = new Db().set(new Text("a.sou"), "one").set(new Text("b.sou"), "xx");
        assertEquals("a.sou", db.ask(new Longest("a.sou", "b.sou")).value());
        // A different text of the same length: the length is recomputed and comes out equal, so
        // nothing that read the length has anything to do.
        db.set(new Text("a.sou"), "two");
        assertEquals("a.sou", db.ask(new Longest("a.sou", "b.sou")).value());
        assertEquals(2, runs("length:a.sou"));
        assertEquals(1, runs("longest"));
    }

    @Test
    void doesNothingWhenTheTextIsSetToWhatItAlreadyWas() {
        Db db = new Db().set(new Text("a.sou"), "one");
        db.ask(new Length("a.sou"));
        db.set(new Text("a.sou"), "one");
        db.ask(new Length("a.sou"));
        assertEquals(1, runs("length:a.sou"));
    }

    @Test
    void reportsWhatTheCurrentAnswersFoundRatherThanEveryAttempt() {
        Db db = new Db().set(new Text("a.sou"), "one");
        db.ask(new Complains("nope"));
        assertEquals(1, db.allReports().size());
        db.set(new Text("a.sou"), "two");
        db.ask(new Complains("nope"));
        assertEquals(1, db.allReports().size(), "the same complaint is not collected twice");
    }

    /** Whether {@link Fragile} still takes the path that cycles and then throws. */
    private static boolean fragile = true;

    /**
     * A key that reaches a cycle and then fails outright — an internal fault, not a compile error,
     * which is what a compile error is a value for. The store has to come out of it as it went in.
     */
    record Fragile(int depth) implements Key<String> {
        @Override
        public Answer<String> compute(Db db) {
            ran("fragile" + depth);
            if (depth == 0) {
                if (!fragile) {
                    return Answer.of("ok");
                }
                db.ask(new Fragile(1));
                throw new IllegalStateException("boom");
            }
            db.ask(new Fragile(0));
            return Answer.of("inner");
        }

        @Override
        public Answer<String> onCycle(List<Key<?>> cycle) {
            return Answer.of("cycle");
        }
    }

    @Test
    void aFailedAnswerLeavesNothingBehind() {
        Db db = new Db();
        assertThrows(IllegalStateException.class, () -> db.ask(new Fragile(0)));

        // The store is used again — a language server keeps one across edits, so a fault in one
        // request must not make every later answer to that question uncacheable.
        fragile = false;
        try {
            assertEquals("ok", db.ask(new Fragile(0)).value());
            db.ask(new Fragile(0));
            assertEquals(2, runs("fragile0"), "the answer after the fault is kept like any other");
        } finally {
            fragile = true;
        }
    }

    @Test
    void reportsWhetherAKeyHasBeenComputed() {
        Db db = new Db().set(new Text("a.sou"), "x");
        assertFalse(db.isComputed(new Shouted("a.sou")));
        db.ask(new Shouted("a.sou"));
        assertTrue(db.isComputed(new Shouted("a.sou")));
    }
}
