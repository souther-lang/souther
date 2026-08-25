package souther.compiler;

import souther.compiler.report.AdequacyReport;
import org.junit.jupiter.api.Test;

import souther.compiler.query.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.OutputCaseEvidence;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Db;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What case a row supplied at an input position, where the position writes its values under a name.
 *
 * <p>A {@code data DecisionN = Decision} is the sum it names. What it divides into is what
 * {@code Decision} divides into, and a row at that position writes {@code DecisionN(Approved { .. })}
 * — so the case it supplied is {@code Approved}, read through the name it is worn under.
 *
 * <p>Which case constructed a value and which case a position sees are two questions. The first is
 * the name the row wrote, and everything that builds the value or holds it against the output's arms
 * needs it to stay that; the second is the one this measure counts. Read one off the other, the two
 * cannot both be right for a position wearing a name.
 */
class SignatureCoverageReadsAPositionThroughItsNamesTest {

    private static final String DECLARATIONS = """
            module demo

            data Ok

            data Approved = { id: Int }
            data Rejected = { why: String }
            data Decision = Approved | Rejected
            data DecisionN = Decision
            data DecisionNN = DecisionN
            data OtherN = Decision

            behavior bare : (decision: Decision) -> Ok
            let bare (decision) = Ok

            behavior wrapped : (decision: DecisionN) -> Ok
            let wrapped (decision) = Ok

            behavior twice : (decision: DecisionNN) -> Ok
            let twice (decision) = Ok

            behavior makes : (id: Int) -> DecisionN
                constructs DecisionN, Approved
            let makes (id) = DecisionN(Approved { id = id })
            """;

    /** A name over a sum divides the position the way the sum it names does. */
    @Test
    void aWrappedSumHasTheCasesTheSumItNamesHas() {
        InputCaseEvidence wrapped = input("""
                example wrapped
                    | (DecisionN(Approved { id = 1 })) -> Ok
                """, "wrapped");

        assertEquals(List.of("Approved", "Rejected"), names(wrapped.declared()));
        assertEquals(MeasurementStatus.COMPLETE, AdequacyReport.statusOf(wrapped.cases()));
    }

    /** The same position, read at the case a row wrote there. */
    @Test
    void aRowUnderTheNameSuppliesTheCaseUnderIt() {
        InputCaseEvidence wrapped = input("""
                example wrapped
                    | (DecisionN(Approved { id = 1 })) -> Ok
                """, "wrapped");

        assertEquals(List.of("Approved"), names(wrapped.seen().specified()));
        assertEquals(List.of("Rejected"), names(wrapped.unspecified()));
    }

    /** Each case, so that neither is the one the reader happens to answer with. */
    @Test
    void eitherCaseUnderTheNameIsTheCaseItSupplies() {
        InputCaseEvidence wrapped = input("""
                example wrapped
                    | (DecisionN(Rejected { why = "no" })) -> Ok
                """, "wrapped");

        assertEquals(List.of("Rejected"), names(wrapped.seen().specified()));
        assertEquals(List.of("Approved"), names(wrapped.unspecified()));
    }

    /**
     * A count and the cases beside it say one thing. A reader answering with the name would land
     * outside the set it is counted in, and both rows would be reported as covering nothing.
     */
    @Test
    void nothingIsSuppliedThatThePositionDoesNotHave() {
        InputCaseEvidence wrapped = input("""
                example wrapped
                    | (DecisionN(Approved { id = 1 })) -> Ok
                    | (DecisionN(Rejected { why = "no" })) -> Ok
                """, "wrapped");

        assertTrue(wrapped.declared().containsAll(wrapped.seen().specified()),
                "what a row supplied is one of the cases the position has: " + wrapped.seen().specified());
        assertEquals(List.of("Approved", "Rejected"), names(wrapped.seen().specified()));
        assertEquals(List.of(), names(wrapped.unspecified()));
    }

    /** The names come off in the order they went on, however many there are. */
    @Test
    void namesComeOffToTheSumHoweverManyAreWorn() {
        InputCaseEvidence twice = input("""
                example twice
                    | (DecisionNN(DecisionN(Approved { id = 1 }))) -> Ok
                """, "twice");

        assertEquals(List.of("Approved", "Rejected"), names(twice.declared()));
        assertEquals(List.of("Approved"), names(twice.seen().specified()));
    }

    /**
     * The name is still what a row constructs. An output written under one is answered with it — the
     * arm a row states there is held against {@code DecisionN} and nothing else — so a reading that
     * took the name off wherever it found one would refuse a row that is right.
     *
     * <p>What that output's cases are is a question this does not answer and did not move: the
     * measure says so rather than counting them.
     */
    @Test
    void anOutputUnderANameIsStillAnsweredWithTheName() {
        String rows = """
                example makes
                    | (1) -> DecisionN(Approved { id = 1 })
                """;

        assertEquals(List.of(), errors(rows));
        Adequacy.SignatureEvidence makes = signatures(rows).get("makes");
        assertEquals(MeasurementStatus.NOT_APPLICABLE, AdequacyReport.statusOf(makes.output().cases()));
        assertEquals(OutputCaseEvidence.NotASum.NOT_A_SUM, makes.output().cases().why());
    }

    /**
     * Only the names the position writes its values under come off. Peeling whatever is there until
     * something recognisable appears would credit a case to a row that named another type, and what
     * a position admits is a question this measure does not get to answer by reading past it.
     *
     * <p>So the row teaches the position nothing: both its cases are still owed a row.
     */
    @Test
    void aNameThePositionDoesNotWriteIsNotComeOffOf() {
        InputCaseEvidence wrapped = input("""
                example wrapped
                    | (OtherN(Approved { id = 1 })) -> Ok
                """, "wrapped");

        assertFalse(names(wrapped.seen().specified()).contains("Approved"),
                "a name the position does not write is not read through: " + wrapped.seen().specified());
        assertEquals(List.of("Approved", "Rejected"), names(wrapped.unspecified()));
    }

    /** A position written as the sum itself is read the way it always was. */
    @Test
    void aBareSumIsUnchanged() {
        InputCaseEvidence bare = input("""
                example bare
                    | (Approved { id = 1 }) -> Ok
                """, "bare");

        assertEquals(List.of("Approved", "Rejected"), names(bare.declared()));
        assertEquals(List.of("Approved"), names(bare.seen().specified()));
    }

    private static InputCaseEvidence input(String rows, String behavior) {
        Map<String, Adequacy.SignatureEvidence> all = signatures(rows);
        Adequacy.SignatureEvidence evidence = all.get(behavior);
        assertEquals(1, evidence.positions().size());
        return evidence.positions().get(0);
    }

    private static Map<String, Adequacy.SignatureEvidence> signatures(String rows) {
        Compilation compilation = measured(rows);
        return compilation.db().ask(new Adequacy.Witnesses(compilation.modules().get(0))).value();
    }

    private static List<String> errors(String rows) {
        List<String> codes = new ArrayList<>();
        for (Db.Found found : measured(rows).db().allReports()) {
            if (found.report().isError()) {
                codes.add(found.report().diagnostic().code());
            }
        }
        return codes;
    }

    private static Compilation measured(String rows) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + "\n" + rows, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static List<String> names(java.util.Collection<TypeSymbol> cases) {
        return cases.stream().map(TypeSymbol::name).toList();
    }
}
