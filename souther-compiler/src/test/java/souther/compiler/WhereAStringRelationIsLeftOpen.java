package souther.compiler;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.StandingQuestion;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a behavior's rules leave open at each place, as the report says it: the places a relation
 * between strings is shown over a region of, each with what is left out of the region.
 */
final class WhereAStringRelationIsLeftOpen {

    private WhereAStringRelationIsLeftOpen() {
    }

    /** What the model says of {@code behavior}, measured as the full report asks it. */
    static PartitionEvidence evidenceOf(String source, String behavior) {
        Compilation compilation = ACompiledModel.measured(source, Adequacy.Asked.fullReport());
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        PartitionEvidence evidence = all.get(behavior);
        assertNotNull(evidence, behavior);
        return evidence;
    }

    /** What the rules of {@code behavior} left open, by the place, each as what is open there. */
    static Map<String, List<BlockReason.RelationShownOverARegion>> leftOpen(String source,
                                                                           String behavior) {
        Map<String, List<BlockReason.RelationShownOverARegion>> out = new TreeMap<>();
        for (PartitionEvidence.Unanswered each : evidenceOf(source, behavior).unanswered()) {
            if (each.asked() instanceof StandingQuestion.RegionUndetermined open) {
                out.computeIfAbsent(open.at().path().toString(), place -> new ArrayList<>())
                        .add(open.filed().why());
            }
        }
        return out;
    }

    /** The places of {@code behavior} the rules left something unread at, whatever it was. */
    static List<String> unreadPlaces(String source, String behavior) {
        return evidenceOf(source, behavior).unanswered().stream()
                .map(each -> each.asked().toString()).sorted().distinct().toList();
    }
}
