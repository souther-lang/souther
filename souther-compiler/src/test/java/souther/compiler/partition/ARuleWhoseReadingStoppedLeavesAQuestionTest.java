package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.conformance.ConformanceCorpus;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every rule whose reading stopped leaves a question standing where it was filed.
 *
 * <p>What the measures rest on. A measure is held open by a question and by nothing else, so a rule
 * this compiler did not finish reading that raises none is one the measure closes over — and it
 * closes silently, because a finding is still published and a reader of the report still sees the
 * rule.
 *
 * <p><b>Asked of every reader that can file one.</b> Which of them owes a question is a decision
 * each of them makes where it files: the accounting of a declaration's clauses raises it, a body's
 * comparison and a clause of an {@code ensures} say instead that nothing classifies them, and the
 * walk that cannot choose which number a position is measured at says so itself. Nothing in the
 * types holds those four to the same answer, so this does — a reader added, or one that starts
 * filing a stop where it used to file a statement, fails here rather than taking a measure quietly
 * with it.
 *
 * <p>Over the models this repository carries and over three written for the readers the corpora do
 * not exercise, since what is being checked is a property of the readers rather than of any one
 * model.
 */
class ARuleWhoseReadingStoppedLeavesAQuestionTest {

    /** A position whose two coordinates are both spoken for, which no accounting decides. */
    private static final String COMPETING_COORDINATES = """
            module probe.competing

            data V = { s: String }
                invariant low = s >= "a"
                invariant long = String.length(s) >= 3

            data Ok

            behavior f : (v: V) -> Ok
            """;

    /** A comparison in a body that no reading takes apart. */
    private static final String A_COMPARISON_NOBODY_READS = """
            module probe.guarded

            data Pair = { x: Int, y: Int }
            data Low
            data High

            behavior pick : (p: Pair) -> Low | High
            let pick (p) =
                if Int.multiply(p.x, p.x) < 10
                    then High
                    else Low
            """;

    /** A clause of an `ensures` stated in a form nothing reads. */
    private static final String AN_ENSURES_NOBODY_READS = """
            module probe.ensures

            data Item = { price: Int }
            data Ok = { at: Int }

            behavior look : (item: Item) -> Ok
                ensures Bool.not(item.price > 100)
            """;

    @Test
    void everyStoppedFindingHasAQuestionAtThePlaceItWasFiled() throws Exception {
        List<String> alone = new ArrayList<>();
        int stopped = 0;
        for (Compilation compilation : every()) {
            for (String module : compilation.modules()) {
                Map<String, PartitionEvidence> coverage =
                        compilation.db().ask(new Adequacy.Coverage(module)).value();
                if (coverage == null) {
                    continue;
                }
                for (PartitionEvidence evidence : coverage.values()) {
                    Set<String> asked = new LinkedHashSet<>();
                    for (PartitionEvidence.Unanswered each : evidence.unanswered()) {
                        asked.add(each.asked().rule() + " @ " + each.at());
                    }
                    for (RuleWithoutALine each : evidence.rulesWithoutALine()) {
                        if (!(each.why() instanceof BlockReason.RuleReadingStopped)) {
                            continue;
                        }
                        stopped++;
                        String where = each.rule() + " @ " + each.at().path();
                        if (!asked.contains(where)) {
                            alone.add(where + " (" + each.why().getClass().getSimpleName() + ")");
                        }
                    }
                }
            }
        }

        assertEquals(List.of(), alone,
                "a rule this compiler did not finish reading, with nothing standing at the place it"
                        + " was filed: the measures close over it and the report still names it");
        assertTrue(stopped > 0, "no reading stopped anywhere, so this checked nothing");
    }

    /** The models this repository carries, and the three readers they do not exercise. */
    private static List<Compilation> every() throws Exception {
        List<Compilation> out = new ArrayList<>();
        for (ConformanceCorpus corpus : ConformanceCorpus.all()) {
            out.add(corpus.analyse().compilation());
        }
        for (String each : List.of(COMPETING_COORDINATES, A_COMPARISON_NOBODY_READS,
                AN_ENSURES_NOBODY_READS)) {
            Compilation one = Compilation.ofSource(each, "Main");
            one.measure(Adequacy.Asked.fullReport());
            one.answerEverything();
            out.add(one);
        }
        Path root = souther.test.RepositoryLayout.ofWorkingDirectory().root();
        for (List<String> corpus : CORPORA) {
            List<String> sources = new ArrayList<>();
            for (String each : corpus) {
                sources.add(Files.readString(root.resolve(each)));
            }
            Compilation compilation =
                    Compilation.ofSources(sources, souther.compiler.meta.ModulePath.EMPTY);
            compilation.answerEverything();
            out.add(compilation);
        }
        return out;
    }

    private static final List<List<String>> CORPORA = List.of(
            List.of("souther-bench/src/main/resources/souther/bench/corpus/crm/crm.sou",
                    "souther-bench/src/main/resources/souther/bench/corpus/crm/pipeline.sou",
                    "souther-bench/src/main/resources/souther/bench/corpus/crm/quoting.sou"),
            List.of("souther-bench/src/main/resources/souther/bench/corpus/issuetracker/issues.sou"),
            List.of("souther-bench/src/main/resources/souther/bench/corpus/runtime/runtime.sou"));
}
