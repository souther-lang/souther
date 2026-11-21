package souther.compiler;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

/**
 * What the document a measured compilation's report writes says of where a run may stop and of
 * what it leaves unread, as its findings say it and not as an English line does: the kind of each
 * finding, what it is about, and for a stop, each operation it is said of and why it is not shown.
 *
 * <p>A finding of the right kind about the wrong thing is no evidence of the right one, so what a
 * test holds is the finding's fields, read off the published words.
 */
public final class StopsTheReportSays {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private StopsTheReportSays() {
    }

    /**
     * One operation a stop is said of: as it is written, or null where the run may stop in
     * something worked out that no operation names; and why neither that it stops nor that it
     * does not is shown, or null where it is shown to stop.
     */
    public record Operation(String written, String unresolvedBecause) {}

    /** A finding that a run reaching the rule {@code subject} names may stop, and the operations
     *  it is said of. */
    public record Stop(String subject, List<Operation> operations) {}

    /** A finding that what a rule states about {@code subject} is not read, and why. */
    public record Unread(String subject, String because) {}

    /** What the document says of {@code compilation}, which has been measured. */
    public record Said(List<Stop> stops, List<Unread> unread) {}

    /** What the report of {@code compilation} says. */
    public static Said of(Compilation compilation) {
        JsonNode document = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<Stop> stops = new ArrayList<>();
        List<Unread> unread = new ArrayList<>();
        collect(document, stops, unread);
        return new Said(List.copyOf(stops), List.copyOf(unread));
    }

    private static void collect(JsonNode node, List<Stop> stops, List<Unread> unread) {
        if (node.isObject()) {
            switch (node.path("kind").asString()) {
                case "rule_may_stop_a_run", "rule_stop_not_shown" -> {
                    List<Operation> operations = new ArrayList<>();
                    node.path("unresolved").forEach(each -> operations.add(new Operation(
                            each.has("operation") ? each.path("operation").asString() : null,
                            each.path("reason").asString())));
                    node.path("everyRunStops").forEach(each -> operations.add(new Operation(
                            each.has("operation") ? each.path("operation").asString() : null,
                            null)));
                    stops.add(new Stop(node.path("subject").asString(), List.copyOf(operations)));
                }
                case "partition_not_read" -> unread.add(new Unread(node.path("subject").asString(),
                        node.path("reason").asString()));
                default -> { }
            }
        }
        node.forEach(child -> collect(child, stops, unread));
    }
}
