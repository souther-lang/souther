package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * One method introduces a measure's answer, and nothing else makes a case of one.
 *
 * <p>{@code PartitionDerivation.of} and {@code BoundaryDerivation.of} are the rule: what a measure
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

    private static final String PARTITION = "souther.compiler.query.PartitionDerivation";
    private static final String BOUNDARY = "souther.compiler.query.BoundaryDerivation";

    /**
     * Every method that makes a case of a measure, and how many it makes.
     *
     * <p>{@code of} is the introduction rule and makes its four: an absence, a measure made in
     * full, one made in part, and one whose reading did not run out. {@code PartitionEvidence}
     * makes the two {@code NoSubject}s of a {@code >->} composition in its static initialiser,
     * which is the one case claiming nothing about a reading and so owing no proof.
     */
    private static final Map<String, Integer> INTRODUCED_BY = new LinkedHashMap<>(Map.of(
            PARTITION + "#of(Ljava/util/List;"
                    + "Lsouther/compiler/partition/MeasureClosure$OfThePartition;)"
                    + "Lsouther/compiler/query/PartitionDerivation;", 4,
            BOUNDARY + "#of(Ljava/util/List;"
                    + "Lsouther/compiler/partition/MeasureClosure$OfTheBorder;)"
                    + "Lsouther/compiler/query/BoundaryDerivation;", 4,
            "souther.compiler.query.PartitionEvidence#<clinit>()V", 2));

    @Test
    void nothingButTheIntroductionRuleMakesACaseOfAMeasure() throws Exception {
        List<String> cases = casesOf(PARTITION, BOUNDARY);

        assertEquals(10, cases.size(), () -> "the cases of the two measures: " + cases);

        Map<String, Integer> made = new LinkedHashMap<>();
        for (Compiled.Site site : Compiled.sites()) {
            for (String each : cases) {
                if (site.makesA(each)) {
                    made.merge(site.at(), 1, Integer::sum);
                }
            }
        }
        assertEquals(INTRODUCED_BY, made, "what makes a case of a measure rather than asking `of`");
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
