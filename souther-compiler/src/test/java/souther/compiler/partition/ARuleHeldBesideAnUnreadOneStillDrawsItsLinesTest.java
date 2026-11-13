package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ReadingPolicy;
import souther.compiler.inputs.RuleWithoutALine;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Front;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.regex.PatternPlan;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule the set of values reads is published as the set it leaves, whatever else is written about
 * the position that the set has no word for.
 *
 * <p>What a rule leaves is the rule's own, and a length written beside a prefix does not make the
 * strings the prefix admits any less the prefix's. Held back for it, the line the prefix draws
 * went missing and the classes of the position came back holding strings the model refuses —
 * where the same two rules written the other way round, or the prefix alone, drew it.
 *
 * <p>What does hold a rule back is the answer not having been built: a position whose answer ran
 * out of allowance has no machine for a rule's set to be made in, and a second allowance would be
 * answering where the first could not.
 */
class ARuleHeldBesideAnUnreadOneStillDrawsItsLinesTest {

    private static final String MODEL = """
            module bounded

            data Code = String invariant %s

            behavior h : (code: Code) -> Int
            let h (Code(code)) =
                if code >= "AM" then 1 else 2

            example h
                | "low"  : (Code("AB")) -> 2
                | "high" : (Code("AZ")) -> 1
            """;

    private static final String THE_PREFIX = "String.startsWith(\"A\", value)";

    private static final String THE_PREFIX_AND_A_LENGTH =
            "String.startsWith(\"A\", value) && String.length(value) <= 5";

    private static final String A_LENGTH_AND_THE_PREFIX =
            "String.length(value) <= 5 && String.startsWith(\"A\", value)";

    @Test
    void aLengthBesideAPrefixLeavesTheLinesThePrefixDraws() {
        List<String> alone = classesOf(MODEL.formatted(THE_PREFIX), ReadAs.WITH_ROOM);

        assertEquals(List.of("code: A <= x < AM", "code: AM <= x < B"), alone,
                "the prefix draws a line at each end of its run");
        assertEquals(alone, classesOf(MODEL.formatted(THE_PREFIX_AND_A_LENGTH), ReadAs.WITH_ROOM));
        assertEquals(alone, classesOf(MODEL.formatted(A_LENGTH_AND_THE_PREFIX), ReadAs.WITH_ROOM));
    }

    @Test
    void andIsNotSaidToBeASetThisCompilerDidNotHandOn() {
        assertEquals(List.of(), reasonsOf(MODEL.formatted(THE_PREFIX_AND_A_LENGTH),
                ReadAs.WITH_ROOM));
    }

    @Test
    void butWhereTheAnswerCouldNotBeBuiltNothingIsPublishedForTheRule() {
        String model = MODEL.formatted(THE_PREFIX_AND_A_LENGTH);

        assertEquals(List.of(), reasonsOf(model, ReadAs.WITH_NO_ROOM_FOR_THE_ANSWER),
                "a set nobody made holds the position to nothing");
        assertEquals(List.of("code: x < AM", "code: AM <= x"),
                classesOf(model, ReadAs.WITH_NO_ROOM_FOR_THE_ANSWER),
                "and only the cut the behavior itself makes is drawn, where the prefix would"
                        + " otherwise have drawn the lines at A and B");
    }

    private static final class ReadAs {

        static final ReadingPolicy WITH_ROOM = souther.compiler.query.ReadAs.THE_COMPILATION_DOES;

        /** An allowance for the answer too small for any machine, and room beside it. */
        static final ReadingPolicy WITH_NO_ROOM_FOR_THE_ANSWER = new ReadingPolicy(
                WITH_ROOM.dnfExpansionLimit(), WITH_ROOM.scalePlacesLimit(),
                new PatternPlan.Budget(1, 1, 1_000_000_000L),
                souther.compiler.values.AsACompilationAllows.whatARuleLeaves());
    }

    private static List<String> reasonsOf(String model, ReadingPolicy policy) {
        List<String> out = new ArrayList<>();
        for (RuleWithoutALine each : evidence(model, policy).rulesWithoutALine()) {
            out.add(each.why().getClass().getSimpleName());
        }
        return out;
    }

    private static List<String> classesOf(String model, ReadingPolicy policy) {
        Measurement<List<PartitionEvidence.AxisCoverage>> measured =
                (Measurement<List<PartitionEvidence.AxisCoverage>>)
                        evidence(model, policy).partitioned();
        List<PartitionEvidence.AxisCoverage> axes = switch (measured) {
            case Measurement.Complete<List<PartitionEvidence.AxisCoverage>> it -> it.value();
            case Measurement.Partial<List<PartitionEvidence.AxisCoverage>> it -> it.value();
            default -> throw new AssertionError("the position was not measured: " + measured);
        };
        List<String> out = new ArrayList<>();
        axes.forEach(axis -> axis.classes().forEach(each -> out.add(each.toString())));
        return out;
    }

    private static PartitionEvidence evidence(String model, ReadingPolicy policy) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.db().set(new Front.Reading(), policy);
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        for (String module : compilation.modules()) {
            Map<String, PartitionEvidence> coverage =
                    compilation.db().ask(new Adequacy.Coverage(module)).value();
            if (coverage != null && coverage.get("h") != null) {
                return coverage.get("h");
            }
        }
        throw new AssertionError("the behavior was not measured");
    }
}
