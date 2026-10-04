package souther.compiler.query;

import souther.compiler.meta.ModulePath;
import souther.compiler.revision.RevisionKnowledge;
import souther.compiler.revision.RevisionWork;
import souther.compiler.source.SourceId;

import org.junit.jupiter.api.Test;

import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Work the revision lends is lent with what doing it read of the store.
 *
 * <p>A piece of revision work is done for the question that asks first and lent to every question
 * after it. A question is kept by what it read, so a question lent the answer alone read nothing to
 * have it, and is kept over an edit to what the work read — it goes on answering out of a world the
 * edit has left. What the work read goes with what it came to, and the question lent it reads the
 * same.
 *
 * <p>Asked of the knowledge every reading under a store borrows ({@link Db#readings}), with work
 * that reads one thing, so that what was read is a set with one thing in it.
 */
class WorkARevisionLendsIsReadForWhoeverItIsLentToTest {

    private static final String BEFORE = """
            module demo exposing ( twice )

            behavior twice : (n: Int) -> Int
            let twice (n) = n * 2
            """;

    private static final String AFTER = """
            module demo exposing ( twice )

            behavior twice : (n: Int) -> Int
            let twice (n) = n + n
            """;

    private static final Front.Text THE_TEXT = new Front.Text(new SourceId("demo.sou"));

    /**
     * Work that reads the source's text out of the store and comes to it.
     *
     * <p>One piece of work whoever asks: the store is carried to do it with and is no part of which
     * work it is.
     */
    private static final class TheText implements RevisionWork<String> {

        private final Db db;

        TheText(Db db) {
            this.db = db;
        }

        @Override
        public String workedOut(RevisionKnowledge revision) {
            return db.ask(THE_TEXT).value();
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof TheText;
        }

        @Override
        public int hashCode() {
            return TheText.class.hashCode();
        }
    }

    /** A question answered with what the work came to, and with nothing else. */
    private record Asking(String name, String who) implements Key<String> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<String> compute(Db db) {
            return Answer.of(db.readings().revision().settled(new TheText(db)));
        }
    }

    private static final Asking FIRST = new Asking("demo", "first");

    private static final Asking SECOND = new Asking("demo", "second");

    @Test
    void aQuestionLentTheWorkReadWhatDoingItRead() {
        Db db = compiled().db();
        long before = RevisionKnowledge.timesDone(TheText.class);
        db.ask(FIRST);
        db.ask(SECOND);

        assertEquals(1, RevisionKnowledge.timesDone(TheText.class) - before,
                "the second question was lent the work rather than doing it");
        assertTrue(db.dependenciesOf(FIRST).contains(THE_TEXT),
                "the question that did the work read what the work read");
        assertTrue(db.dependenciesOf(SECOND).contains(THE_TEXT),
                "and so did the question it was lent to");
    }

    /**
     * And an edit to what the work read reaches the question it was lent to.
     *
     * <p>The consequence and not only the record of it: a question that read nothing is still the
     * answer it was, and asked after the edit would hand back the text the edit replaced.
     */
    @Test
    void anEditToWhatTheWorkReadReachesTheQuestionItWasLentTo() {
        Compilation compilation = compiled();
        Db db = compilation.db();
        assertEquals(BEFORE, db.ask(FIRST).value());
        assertEquals(BEFORE, db.ask(SECOND).value(), "lent what the first question worked out");

        compilation.update(Map.of("demo.sou", AFTER), Set.of());

        assertEquals(AFTER, db.ask(SECOND).value(),
                "the question lent the work is answered out of the text as it now reads");
    }

    private static Compilation compiled() {
        return Compilation.ofDocuments(Map.of("demo.sou", BEFORE), Set.of(), ModulePath.EMPTY);
    }
}
