package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A closure written on the way to a comparison, whether as an argument beside the one the
 * comparison stands in or bound by a {@code let}, makes a function and runs nothing of its body
 * there. The call that applies it does that, after every argument it is handed, so what it may
 * stop a run on is no stop on the way to the comparison.
 *
 * <p>{@code List.map(d -> Past { ... }, List.filter(d -> ..., asked(intent)))} makes the list the
 * filter keeps before the map applies its closure. The filter's comparison is reached by the cases
 * the match gives an element for, whatever the map's closure builds from them: it is read, the
 * measure of the intent has no class short of a row, and the examples that reach each case still
 * reach it.
 */
class AClosureBesideAComparisonIsNotWorkedOutBeforeItTest {

    private static final String EXAMPLES = """
            example reasons
                | "past" : (Request { convertedOn = Date("2026-08-10"), intent = Asked { closeDate = Date("2026-08-01") } })
                    -> [ Past { requested = Date("2026-08-01") } ]
                | "future" : (Request { convertedOn = Date("2026-08-10"), intent = Asked { closeDate = Date("2026-09-01") } })
                    -> [ ]
                | "none" : (Request { convertedOn = Date("2026-08-10"), intent = NoAsk }) -> [ ]
            """;

    private static PartitionEvidence evidenceOf(String body) {
        String model = """
                module probe

                data Asked = { closeDate: Date }
                data NoAsk
                data Intent = NoAsk | Asked

                data Request = { convertedOn: Date, intent: Intent }

                data Past = { requested: Date }

                behavior reasons : (request: Request) -> List<Past>
                    constructs Past

                let asked (intent: Intent): List<Date> =
                    match intent with
                        | NoAsk -> []
                        | Asked { closeDate } -> [ closeDate ]

                let reasons (request) =
                    %s

                %s
                """.formatted(body, EXAMPLES);
        return measured(model);
    }

    private static PartitionEvidence measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db().ask(new Adequacy.Coverage("probe")).value().get("reasons");
    }

    /** Where a reading of a rule stopped or was left unclassified. */
    private static List<String> unreadAt(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.readingStopped()
                        || each instanceof PartitionEvidence.NotRead.AnUnclassifiedRule)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /**
     * The comparison was read to the end: nothing in the model is left short, both of its sides
     * are filed where they stand, and the two classes of the intent the examples write are each
     * reached by a row of them.
     */
    private static void assertRead(PartitionEvidence evidence) {
        String shown = evidence.notRead().toString();
        assertEquals(List.of(), unreadAt(evidence), () -> shown);
        assertEquals(List.of("request.convertedOn", "request.intent@Asked.closeDate"),
                evidence.notRead().stream().map(PartitionEvidence.NotRead::at).sorted().distinct()
                        .toList(), () -> shown);
        if (!(evidence.partitioned()
                instanceof Measurement.Complete<List<PartitionEvidence.AxisCoverage>> complete)) {
            throw new AssertionError("the model is read in full: " + shown);
        }
        PartitionEvidence.AxisCoverage intent = complete.value().stream()
                .filter(axis -> axis.path().equals("request.intent")).findFirst().orElseThrow();
        assertEquals(List.of("NoAsk", "Asked"), intent.classes());
        if (!(intent.reached()
                instanceof Measurement.Complete<PartitionEvidence.AxisCoverage.Reached> reached)) {
            throw new AssertionError("each class of the intent is reached by a row: " + shown);
        }
        assertEquals(Set.of("NoAsk", "Asked"), reached.value().covered());
        assertEquals(0, reached.value().unclassifiedRows());
    }

    @Test
    void aMapOverAFilterReadsTheFilterComparisonWhereAMatchMadeItsList() {
        assertRead(evidenceOf("""
                List.map(d -> Past { requested = d },
                         List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                     asked(request.intent)))"""));
        assertRead(evidenceOf("""
                List.map(d -> Past { requested = d },
                         List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                     match request.intent with
                                         | NoAsk -> []
                                         | Asked { closeDate } -> [ closeDate ]))"""));
    }

    /**
     * A match that gives an element on some cases only: the step is reached on those and on no
     * other, so the comparison is asked at the element each of them gives and at none the other
     * case could be asked at.
     */
    @Test
    void aMatchGivingAnElementOnSomeCasesOnlyLetsOnlyThoseCasesReachTheStep() {
        String model = """
                module probe

                data Asked = { closeDate: Date }
                data Moved = { closeDate: Date }
                data NoAsk
                data Intent = NoAsk | Asked | Moved

                data Request = { convertedOn: Date, intent: Intent }

                data Past = { requested: Date }

                behavior reasons : (request: Request) -> List<Past>
                    constructs Past

                let asked (intent: Intent): List<Date> =
                    match intent with
                        | NoAsk -> []
                        | Asked { closeDate } -> [ closeDate ]
                        | Moved { closeDate } -> [ closeDate ]

                let reasons (request) =
                    List.map(d -> Past { requested = d },
                             List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                         asked(request.intent)))
                """;
        PartitionEvidence evidence = measured(model);
        String shown = evidence.notRead().toString();
        assertEquals(List.of(), unreadAt(evidence), () -> shown);
        assertEquals(List.of("request.convertedOn", "request.intent@Asked.closeDate",
                        "request.intent@Moved.closeDate"),
                evidence.notRead().stream().map(PartitionEvidence.NotRead::at).sorted().distinct()
                        .toList(), () -> shown);
    }

    /** A closure bound by a {@code let} is the same function value as one written in place. */
    @Test
    void aClosureBoundByALetBesideTheComparisonIsReadTheSame() {
        assertRead(evidenceOf("""
                {
                    let project = d -> Past { requested = d }
                    List.map(project,
                             List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                         asked(request.intent)))
                }"""));
    }

    /**
     * The closure that builds the list the filter walks is applied before the filter's comparison,
     * and the construction in it may stop a run on the dates it is handed. Bound by a {@code let}
     * and handed to the call that makes the list, it is the same.
     */
    @Test
    void aClosureAppliedBeforeTheComparisonStillMayStopARunOnTheWayToIt() {
        List<String> both = List.of("request.convertedOn", "request.intent@Asked.closeDate");
        PartitionEvidence written = evidenceOf("""
                List.filter(p -> Date.daysBetween(request.convertedOn, p.requested) < 0,
                            List.map(d -> Past { requested = d }, asked(request.intent)))""");
        assertEquals(both, unreadAt(written), () -> written.notRead().toString());
        PartitionEvidence bound = evidenceOf("""
                {
                    let project = d -> Past { requested = d }
                    List.filter(p -> Date.daysBetween(request.convertedOn, p.requested) < 0,
                                List.map(project, asked(request.intent)))
                }""");
        assertEquals(both, unreadAt(bound), () -> bound.notRead().toString());
    }
}
