package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.BodyDistinction;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A condition on a name every case of a sum spreads is about the position the name stands at under
 * each case — and only under the cases a row taking the way it is on can be.
 *
 * <p>What the body tells apart at a position is what the ways through it admit there. A fork on
 * {@code r.q.flag} reached only once {@code r.q} was found to be an {@code A} tells {@code A}'s flag
 * apart and says nothing of {@code B}'s: no row that is a {@code B} gets there. And a comparison of
 * a number the cases share draws its line under each case, so the body tells that number apart
 * wherever the comparison can be met.
 */
class AConditionAtANameTheCasesShareIsPlacedWhereItsWayCanStandTest {

    private static final String MODEL = """
            module probe.place

            data Yes
            data No
            data Flag = Yes | No
            data Common = { flag: Flag, count: Int }
                invariant count >= 0 && count <= 10
            data A = { ...Common, a: Int }
            data B = { ...Common, b: Int }
            data Q = A | B
            data Req = { q: Q }

            behavior anywhere : (r: Req) -> String
            let anywhere (r) =
                match r.q.flag with
                    | Yes -> "yes"
                    | No -> "no"

            behavior onceAnA : (r: Req) -> String
            let onceAnA (r) =
                match r.q with
                    | A ->
                        match r.q.flag with
                            | Yes -> "yes"
                            | No -> "no"
                    | B -> "b"

            behavior counted : (r: Req) -> String
            let counted (r) = if r.q.count > 3 then "many" else "few"
            """;

    @Test
    void aForkOnTheNameTellsTheFlagApartUnderEveryCase() {
        Map<String, BodyDistinction> told = toldApart("anywhere");
        assertEquals(2, groups(told.get("r.q@A.flag")), () -> told.toString());
        assertEquals(2, groups(told.get("r.q@B.flag")), () -> told.toString());
    }

    /** The way to the inner fork is a row that is an {@code A}, so {@code B}'s flag is not met. */
    @Test
    void aForkReachedOnlyUnderOneCaseTellsApartOnlyThatCasesFlag() {
        Map<String, BodyDistinction> told = toldApart("onceAnA");
        assertEquals(2, groups(told.get("r.q@A.flag")), () -> told.toString());
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("r.q@B.flag"),
                () -> "no way through a B reaches the fork: " + told);
    }

    /** A comparison of the shared number divides it under each case, and is read there. */
    @Test
    void aComparisonOfTheNameIsReadUnderEveryCase() {
        Map<String, BodyDistinction> told = toldApart("counted");
        for (String count : List.of("r.q@A.count", "r.q@B.count")) {
            assertInstanceOf(BodyDistinction.Drawn.class, told.get(count),
                    () -> count + " is divided by the comparison: " + told);
            assertEquals(2, groups(told.get(count)), () -> told.toString());
        }
    }

    private static int groups(BodyDistinction told) {
        return assertInstanceOf(BodyDistinction.Drawn.class, told).groups().size();
    }

    private static Map<String, BodyDistinction> toldApart(String behavior) {
        Compilation c = Compilation.ofSource(MODEL, "Main");
        c.measure(Adequacy.Asked.fullReport());
        c.answerEverything();
        assertEquals(List.of(), c.errors().stream()
                .map(e -> e.diagnostic().code() + " " + e.diagnostic().said()).toList(),
                "the model is measured");
        PartitionEvidence partition = c.db().ask(new Adequacy.Coverage("probe.place")).value()
                .get(behavior);
        return partition.axes().stream().collect(Collectors.toMap(
                PartitionEvidence.AxisCoverage::name, PartitionEvidence.AxisCoverage::toldApart));
    }
}
