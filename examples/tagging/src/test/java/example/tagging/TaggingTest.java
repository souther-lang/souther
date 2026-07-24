package example.tagging;

import net.unit8.raoh.Err;
import net.unit8.raoh.Ok;
import net.unit8.raoh.Path;
import net.unit8.raoh.Result;

import org.junit.jupiter.api.Test;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * Runs tags.sou's issue-tracker behaviors over the domain, exercising the Set and Map stdlib modules
 * and Some(Assignee(name)) destructuring. Set / Map values have no literal syntax, so verification is
 * here (decode JSON array -> Set, JSON object -> Map, apply, read back through the encoder) rather than
 * in `.sou` `example` blocks.
 */
class TaggingTest {

    private static <T> T ok(Result<T> r) {
        if (r instanceof Err<T> e) {
            throw new AssertionError("should decode: " + e.issues().asList());
        }
        return ((Ok<T>) r).value();
    }

    private RawLabels rawLabels(String text) {
        return ok(RawLabels.decoder().decode(Map.of("text", text), Path.ROOT));
    }

    private Label label(String s) {
        return ok(Label.decoder().decode(s, Path.ROOT));
    }

    /** assignee == null builds an issue with no assignee (the key is omitted → None). */
    private Issue issue(String id, String title, List<String> labels, String assignee) {
        Map<String, Object> m = new HashMap<>();
        m.put("id", id);
        m.put("title", title);
        m.put("labels", labels);
        if (assignee != null) {
            m.put("assignee", assignee);
        }
        return ok(Issue.decoder().decode(m, Path.ROOT));
    }

    @Test
    void normalizeLabelsLowercasesAndDeduplicates() {
        // "Bug, UI, bug" → trim + lowercase each → {"bug", "ui"} (the duplicate "bug" collapses in the Set).
        Object result = NormalizeLabels.of().apply(rawLabels("Bug, UI, bug"));

        LabelSet set = assertInstanceOf(LabelSet.class, result);
        List<?> labels = (List<?>) LabelSet.encoder().encode(set).get("labels");
        assertEquals(Set.of("bug", "ui"), Set.copyOf(labels), "the Set dedups the repeated label");
        assertEquals(2, labels.size());
    }

    @Test
    void blankInputHasNoLabels() {
        assertInstanceOf(NoLabels.class, NormalizeLabels.of().apply(rawLabels("  , ,,  ")));
    }

    @Test
    void assigneeOfOpensSomeAndNone() {
        // Some(Assignee(name)) destructuring binds the bare name.
        Object assigned = AssigneeOf.of().apply(issue("i-1", "Login broken", List.of("bug"), "alice"));
        Assigned a = assertInstanceOf(Assigned.class, assigned);
        assertEquals("alice", Assigned.encoder().encode(a).get("name"));

        // No assignee → the None arm.
        Object unassigned = AssigneeOf.of().apply(issue("i-2", "Typo", List.of("docs"), null));
        assertInstanceOf(Unassigned.class, unassigned);
    }

    @Test
    void addLabelInsertsIntoTheSet() {
        Issue before = issue("i-1", "Login broken", List.of("bug"), "alice");
        Object after = AddLabel.of().apply(before, label("ui"));

        Issue result = assertInstanceOf(Issue.class, after);
        List<?> labels = (List<?>) Issue.encoder().encode(result).get("labels");
        assertEquals(Set.of("bug", "ui"), Set.copyOf(labels));
    }

    @Test
    void countByLabelCountsAcrossTheBoard() {
        Board board = ok(Board.decoder().decode(Map.of("issues", List.of(
                Map.of("id", "i-1", "title", "Login broken", "labels", List.of("bug", "ui")),
                Map.of("id", "i-2", "title", "Crash on save", "labels", List.of("bug")))),
                Path.ROOT));

        Object result = CountByLabel.of().apply(board);
        LabelCounts counts = assertInstanceOf(LabelCounts.class, result);
        @SuppressWarnings("unchecked")
        Map<String, Object> byLabel = (Map<String, Object>) LabelCounts.encoder().encode(counts).get("counts");
        assertEquals(2L, ((Number) byLabel.get("bug")).longValue(), "bug is on both issues");
        assertEquals(1L, ((Number) byLabel.get("ui")).longValue(), "ui is on one");
    }
}
