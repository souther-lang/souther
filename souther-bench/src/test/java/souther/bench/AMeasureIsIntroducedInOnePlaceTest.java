package souther.bench;

import souther.compiler.query.PartitionDerivation;
import souther.compiler.query.BoundaryDerivation;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One method introduces a measure's answer, and nothing else makes a case of one.
 *
 * <p>Every measure's {@code of} is the rule: what a measure
 * came to follows from what it found and whether its own reading ran out, and those two facts
 * arrive together or not at all. A caller writing {@code new Complete(entries)} decides it from the
 * entries alone, which is the reconstruction the type exists to stop — and is what every reader did
 * while the answer was a list beside a status.
 *
 * <p>The type cannot forbid it. {@code Absent} takes the proof that its own measure's reading ran
 * out, and only the reading can make one; {@code Complete} claims the same thing and carries
 * entries instead, so a case public enough to match on is public enough to write. A proof on
 * {@code Complete} as well would close it, at the price of every fixture that wants a measure made
 * in full needing a reading to have made one — which the tests that fabricate a border to hold a
 * criterion to cannot pay. So this is the whole of what enforces the rule.
 *
 * <p>Which is why it asks {@link Compiled} rather than reading the classes itself. Making a value is
 * three things in bytecode and not one, and a check that knew about {@code new} alone would be
 * passed by a constructor reference — the vocabulary belongs in the one place that has it, not in
 * each check that needs it.
 *
 * <p><b>By the method, with its parameters.</b> The rule names {@code of}. Counted per class, a
 * helper beside it would keep the class's total where it was and answer for nothing; counted per
 * name, an overload would be admitted without anybody deciding it should be.
 */
class AMeasureIsIntroducedInOnePlaceTest {

    private static final String MEASUREMENT = "souther.compiler.query.Measurement";

    /**
     * Every method that makes a state of a measurement, and how many it makes.
     *
     * <p>One entry per measure's introduction rule, and nothing else. Each of the nine measures has
     * one method that decides between the states from what it found and what its reading came to —
     * {@code of} where there is a choice to make, and a named factory for each answer a caller can
     * ask for outright ({@code none}, {@code noRows}, {@code noSubject}, {@code truncated}).
     * A caller writing {@code new Complete(...)} would decide it from the entries alone, which is
     * the reconstruction the type exists to stop.
     *
     * <p><b>By the method, with its parameters.</b> Counted per class, a helper beside one would
     * keep the class's total where it was and answer for nothing; counted per name, an overload
     * would be admitted without anybody deciding it should be.
     *
     * <p>{@code PairSpace}'s static initialiser makes the one space that is measured in full and
     * holds nothing — a behavior with no pair of positions — and {@code ItemAssessment} makes the
     * answer a point nobody is owed a row at has. Both are answers about the model rather than
     * readings of it, which is why neither goes through a reading.
     */
    private static final Map<String, Integer> INTRODUCED_BY = new LinkedHashMap<>(
            Map.ofEntries(
            Map.entry("souther.compiler.query.Coverages#pairsOf(Ljava/lang/String;Ljava/util/List;Lsouther/compiler/query/Coverages$Readings;)Lsouther/compiler/query/PartitionEvidence$PairSpace;", 2),
            Map.entry("souther.compiler.query.Coverages#coverageOf(Lsouther/compiler/partition/Axis;Lsouther/compiler/query/Coverages$Readings;)Lsouther/compiler/query/PartitionEvidence$AxisCoverage;", 2),
            Map.entry("souther.compiler.query.Coverages#verdictOf(Lsouther/compiler/query/Coverages$Met;ZLsouther/compiler/partition/Border;Lsouther/compiler/query/Adequacy$Observed;)Lsouther/compiler/query/Measurement;", 3),
            Map.entry("souther.compiler.query.Coverages#whyNoGuardLine(Lsouther/compiler/query/Adequacy$Observed;Z)Lsouther/compiler/query/Measurement;", 2),
            Map.entry("souther.compiler.query.Coverages#whyNoInvariantLine(Ljava/util/List;Z)Lsouther/compiler/query/Measurement;", 1),
            Map.entry("souther.compiler.query.PartitionDerivation#noSubject()Lsouther/compiler/query/Measurement;", 1),
            Map.entry("souther.compiler.query.PartitionDerivation#of(Ljava/util/List;Lsouther/compiler/partition/MeasureClosure$OfThePartition;)Lsouther/compiler/query/Measurement;", 4),
            Map.entry("souther.compiler.query.OutputCaseEvidence#none()Lsouther/compiler/query/OutputCaseEvidence;", 1),
            Map.entry("souther.compiler.query.OutputCaseEvidence#of(Ljava/lang/String;Ljava/util/Set;Lsouther/compiler/query/OutputCaseEvidence$Cases;)Lsouther/compiler/query/OutputCaseEvidence;", 2),
            Map.entry("souther.compiler.query.InputCaseEvidence#none(I)Lsouther/compiler/query/InputCaseEvidence;", 1),
            Map.entry("souther.compiler.query.InputCaseEvidence#of(Ljava/lang/String;ILjava/util/Set;Ljava/util/Set;Lsouther/compiler/query/InputCaseEvidence$Cases;)Lsouther/compiler/query/InputCaseEvidence;", 2),
            Map.entry("souther.compiler.query.BoundaryDerivation#noSubject()Lsouther/compiler/query/Measurement;", 1),
            Map.entry("souther.compiler.query.BoundaryDerivation#of(Ljava/util/List;Lsouther/compiler/partition/MeasureClosure$OfTheBorder;)Lsouther/compiler/query/Measurement;", 4),
            Map.entry("souther.compiler.query.Adequacy$SignatureEvidence#notASum(Lsouther/compiler/query/OutputCaseEvidence;Ljava/util/List;)Lsouther/compiler/query/Adequacy$SignatureEvidence;", 1),
            Map.entry("souther.compiler.query.Adequacy$SignatureEvidence#noRows(Lsouther/compiler/query/OutputCaseEvidence;Ljava/util/List;)Lsouther/compiler/query/Adequacy$SignatureEvidence;", 1),
            Map.entry("souther.compiler.query.Adequacy$SignatureEvidence#of(Lsouther/compiler/query/OutputCaseEvidence;Ljava/util/List;Lsouther/compiler/query/WeakeningSet;)Lsouther/compiler/query/Adequacy$SignatureEvidence;", 2),
            Map.entry("souther.compiler.query.PartitionEvidence$AxisCoverage#noRows(Ljava/lang/String;Ljava/lang/String;Ljava/util/List;Lsouther/compiler/query/PartitionEvidence$AxisCoverage$Reading;)Lsouther/compiler/query/PartitionEvidence$AxisCoverage;", 1),
            Map.entry("souther.compiler.query.PartitionEvidence$PairSpace#noRows(I)Lsouther/compiler/query/PartitionEvidence$PairSpace;", 1),
            Map.entry("souther.compiler.query.PartitionEvidence$PairSpace#truncated(Ljava/lang/String;JI)Lsouther/compiler/query/PartitionEvidence$PairSpace;", 1),
            Map.entry("souther.compiler.query.PartitionEvidence$PairSpace#<clinit>()V", 1),
            Map.entry("souther.compiler.query.Adequacy$BranchEvidence#noBody()Lsouther/compiler/query/Adequacy$BranchEvidence;", 1),
            Map.entry("souther.compiler.query.Adequacy$BranchEvidence#notAsked(Lsouther/compiler/query/Adequacy$BranchEvidence$NotAsked;)Lsouther/compiler/query/Adequacy$BranchEvidence;", 1),
            Map.entry("souther.compiler.query.Adequacy$BranchEvidence#unreadable(Lsouther/compiler/query/WeakeningSet;)Lsouther/compiler/query/Adequacy$BranchEvidence;", 1),
            Map.entry("souther.compiler.query.Adequacy$BranchEvidence#measured(Ljava/lang/String;Ljava/util/List;Ljava/util/Set;Lsouther/compiler/check/PathReachability$Answers$AsRun;Lsouther/compiler/query/WeakeningSet;)Lsouther/compiler/query/Adequacy$BranchEvidence;", 2),
            Map.entry("souther.compiler.query.ItemAssessment#weakeningSource()Lsouther/compiler/query/Measurement;", 1)));

    @Test
    void nothingButTheIntroductionRuleMakesACaseOfAMeasure() throws Exception {
        List<String> cases = casesOf(MEASUREMENT);

        assertEquals(5, cases.size(), () -> "the states of a measurement: " + cases);

        Map<String, Integer> made = new LinkedHashMap<>();
        for (Compiled.Site site : Compiled.sites()) {
            for (String each : cases) {
                if (site.makesA(each)) {
                    made.merge(site.at(), 1, Integer::sum);
                }
            }
        }
        assertEquals(INTRODUCED_BY, made, () -> "what makes a state of a measurement: " + made);
    }

    /**
     * The cases as the type says they are.
     *
     * <p>Asked of the sealed interface rather than listed, so a case added is one this counts
     * without being told — and a case renamed does not quietly leave the set.
     */
    private static List<String> casesOf(String... measures) throws ClassNotFoundException {
        List<String> out = new ArrayList<>();
        for (String measure : measures) {
            for (Class<?> each : Class.forName(measure).getPermittedSubclasses()) {
                out.add(each.getName());
            }
        }
        return out;
    }
}
