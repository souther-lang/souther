package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A closure written beside the argument a comparison stands in is applied after that argument is
 * worked out, so what it may stop a run on is no stop on the way to the comparison.
 *
 * <p>{@code List.map(d -> Past { ... }, List.filter(d -> ..., asked(intent)))} makes the list the
 * filter keeps before the map applies its closure. The filter's comparison is reached by the cases
 * the match gives an element for, whatever the map's closure builds from them.
 */
class AClosureBesideAComparisonIsNotWorkedOutBeforeItTest {

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
                """.formatted(body);
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage("probe")).value().get("reasons");
        return evidence;
    }

    /** Where a relation was read and a run may stop on the way to it. */
    private static List<String> notReachedAtEveryValue(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    @Test
    void aMapOverAFilterReadsTheFilterComparisonWhereAMatchMadeItsList() {
        PartitionEvidence helper = evidenceOf("""
                List.map(d -> Past { requested = d },
                         List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                     asked(request.intent)))""");
        assertEquals(List.of(), notReachedAtEveryValue(helper), () -> helper.notRead().toString());
        PartitionEvidence inline = evidenceOf("""
                List.map(d -> Past { requested = d },
                         List.filter(d -> Date.daysBetween(request.convertedOn, d) < 0,
                                     match request.intent with
                                         | NoAsk -> []
                                         | Asked { closeDate } -> [ closeDate ]))""");
        assertEquals(List.of(), notReachedAtEveryValue(inline),
                () -> inline.notRead().toString());
    }

    /**
     * The closure that builds the list the filter walks is applied before the filter's comparison,
     * and the construction in it may stop a run on the dates it is handed.
     */
    @Test
    void aClosureAppliedBeforeTheComparisonStillMayStopARunOnTheWayToIt() {
        PartitionEvidence evidence = evidenceOf("""
                List.filter(p -> Date.daysBetween(request.convertedOn, p.requested) < 0,
                            List.map(d -> Past { requested = d }, asked(request.intent)))""");
        assertEquals(List.of("request.convertedOn", "request.intent@Asked.closeDate"),
                notReachedAtEveryValue(evidence), () -> evidence.notRead().toString());
    }
}
