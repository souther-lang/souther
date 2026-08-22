package souther.compiler;

import souther.compiler.report.AdequacyReport;
import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a behavior's rows establish about the cases in its signature.
 *
 * <p>The three sets are the point. A case somebody wrote a row for, a case the behavior was seen to
 * produce, and a case a row confirmed it produces are three different claims, and an adequacy report
 * that answers "covered?" with one number cannot tell an author which of them is missing.
 */
class CompileExampleWitnessTest {

    private static final String BASE = """
            module example.member
            import String ( length )

            data MemberId = String
                invariant length(value) > 0

            data Found = { id: MemberId }
            data Missing = { reason: String }

            data Active
            data Suspended
            data Status = Active | Suspended

            behavior lookup : (id: MemberId, status: Status) -> Found | Missing
                constructs Found, Missing

            let lookup (id, status) =
                match status with
                    | Active    -> Found { id = id }
                    | Suspended -> Missing { reason = "suspended" }
            """;

    private static Map<String, Adequacy.SignatureEvidence> evidence(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Map<String, Adequacy.SignatureEvidence> out = compilation.db()
                .ask(new Adequacy.Witnesses(compilation.modules().get(0))).value();
        assertNotNull(out, "the witnesses of a module that compiled");
        return out;
    }

    private static List<String> names(java.util.Set<TypeSymbol> cases) {
        return cases.stream().map(TypeSymbol::name).sorted().toList();
    }

    /** A row that disagreed is no evidence for what it expected and is evidence for what it saw. */
    @Test
    void whatARowExpectsAndWhatItSawAreCountedApart() {
        Adequacy.SignatureEvidence lookup = evidence(BASE + """

                example lookup
                    | "active"    : (MemberId("m-1"), Active)    -> Found { id = MemberId("m-1") }
                    | "suspended" : (MemberId("m-1"), Suspended) -> Found { id = MemberId("m-1") }
                """).get("lookup");

        assertEquals(List.of("Found", "Missing"), names(lookup.output().declared()));
        assertEquals(List.of("Found"), names(lookup.output().seen().specified()),
                "both rows expect Found");
        assertEquals(List.of("Found", "Missing"), names(lookup.output().seen().observed()),
                "the second row saw Missing even though it wanted Found");
        assertEquals(List.of("Found"), names(lookup.output().seen().verified()),
                "only the row that held confirms anything");
        assertEquals(List.of("Missing"), lookup.output().unspecified().stream()
                .map(TypeSymbol::name).toList());
    }

    @Test
    void aPendingRowReachesSpecifiedAndNoFurther() {
        Adequacy.SignatureEvidence findMember = evidence("""
                module example.member
                import String ( length )

                data MemberId = String
                    invariant length(value) > 0

                data Found = { id: MemberId }
                data Missing = { reason: String }

                behavior findMember : (id: MemberId) -> Found | Missing

                example findMember
                    | (MemberId("m-1")) -> Found { id = MemberId("m-1") }
                    | (MemberId("m-9")) -> Missing { reason = "none" }
                """).get("findMember");

        assertEquals(List.of("Found", "Missing"), names(findMember.output().seen().specified()));
        assertEquals(List.of(), names(findMember.output().seen().observed()),
                "nothing ran, so nothing was seen");
        assertEquals(List.of(), names(findMember.output().seen().verified()));
    }

    @Test
    void anInputThatIsASumIsCoveredCaseByCase() {
        Adequacy.SignatureEvidence lookup = evidence(BASE + """

                example lookup
                    | (MemberId("m-1"), Active) -> Found { id = MemberId("m-1") }
                """).get("lookup");

        assertEquals(2, lookup.inputs().size());
        assertEquals(List.of(), names(lookup.inputs().get(0).declared()),
                "a parameter that is not a sum has nothing to cover");
        assertEquals(List.of("Active", "Suspended"), names(lookup.inputs().get(1).declared()));
        assertEquals(List.of("Active"), names(lookup.inputs().get(1).seen().specified()));
        assertEquals(List.of("Suspended"), lookup.inputs().get(1).unspecified().stream()
                .map(TypeSymbol::name).toList());
    }

    @Test
    void aBehaviorWithNoRowsIsNotMeasured() {
        Adequacy.SignatureEvidence lookup = evidence(BASE).get("lookup");

        assertEquals(MeasurementStatus.NOT_MEASURED, AdequacyReport.statusOf(lookup.counted()),
                "no rows is an absence of evidence, not a set of gaps");
    }

    /**
     * An expectation the text does not name a case for — a helper's answer — leaves the row
     * unclassified rather than uncounted, and while there is one a missing case is undecided.
     */
    @Test
    void aRowWhoseCaseCannotBeReadMakesTheMeasurementPartial() {
        Adequacy.SignatureEvidence lookup = evidence(BASE + """

                let asFound (id: MemberId) = Found { id = id }

                example lookup
                    | (MemberId("m-1"), Active) -> asFound(MemberId("m-1"))
                """).get("lookup");

        assertEquals(1, lookup.output().seen().unclassifiedRows());
        assertEquals(MeasurementStatus.PARTIAL, AdequacyReport.statusOf(lookup.output().cases()));
        assertEquals(MeasurementStatus.PARTIAL, AdequacyReport.statusOf(lookup.counted()));
        assertTrue(lookup.output().seen().verified().isEmpty()
                        || names(lookup.output().seen().verified()).equals(List.of("Found")),
                "whatever the row confirmed, it did not confirm a case the text names");
    }
}
