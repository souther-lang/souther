package souther.compiler;

import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value the module states by a {@code let} and the same value written out are one input of a
 * row, so a row the author wrote is not offered again under the other spelling and one input is not
 * offered twice.
 */
class ARowIsTheSameRowWhetherItNamesAValueOrWritesItOutTest {

    private static final String MODEL = """
            module m

            data Shot = Hit | Miss

            data Hit = Int
                invariant value >= 0 && value <= 12

            data Shots = List<Shot>

            behavior points : (s: Shot) -> Int

            let points (s) =
                match s with
                    | Hit as h -> h.value
                    | Miss -> 0

            example points
                | (Hit(0)) -> 0
                | (Hit(12)) -> 12
                | (Miss) -> 0

            behavior total : (shots: Shots) -> Int

            let total (shots) = List.fold((acc, s) -> acc + points(s), 0, shots.value)

            example total
                | (Shots([])) -> 0
                | (Shots([Hit(5), Hit(5)])) -> 10
                | (Shots([Miss])) -> 0

            behavior record : (shots: Shots, next: Shot) -> Shots | Closed

            let record (shots, next) =
                if total(shots) >= 50 then Closed else Shots(List.append(shots.value, [next]))

            """;

    private static final String NOTHING = """
            let nothing: Shot = Hit(0)

            """;

    private static final String WRITTEN_WITH_THE_NAME = MODEL + NOTHING + """
            example record
                | "first" : (Shots([]), nothing) -> Shots([Hit(0)])
            """;

    private static final String WRITTEN_OUT = MODEL + NOTHING + """
            example record
                | "first" : (Shots([]), Hit(0)) -> Shots([Hit(0)])
            """;

    private static final String FIFTY = MODEL + """
            let fifty: Shots = Shots([Hit(12), Hit(12), Hit(12), Hit(12), Hit(2)])

            example total
                | (fifty) -> 50

            example record
                | (fifty, Hit(1)) -> Closed
            """;

    @Test
    void aRowWrittenWithTheNameIsNotOfferedAgain() {
        assertTrue(!meanings(WRITTEN_WITH_THE_NAME).contains("Shots([]), Hit(0)"),
                () -> "record(Shots([]), nothing) is written: " + meanings(WRITTEN_WITH_THE_NAME));
    }

    @Test
    void aRowWrittenOutIsNotOfferedAgainByTheName() {
        assertTrue(!meanings(WRITTEN_OUT).contains("Shots([]), Hit(0)"),
                () -> "record(Shots([]), Hit(0)) is written: " + meanings(WRITTEN_OUT));
    }

    @Test
    void oneInputIsOfferedOnceWhetherTheNameOrTheValueIsWrittenForIt() {
        List<String> meant = meanings(FIFTY);
        assertEquals(meant.stream().distinct().toList(), meant,
                () -> "no input is offered twice: " + offered(FIFTY));
    }

    private static List<String> meanings(String source) {
        return rowsOfRecord(source).stream()
                .map(inputs -> String.join(", ", inputs.stream().map(FixtureTemplate::meaning).toList()))
                .toList();
    }

    private static List<String> offered(String source) {
        return rowsOfRecord(source).stream()
                .map(inputs -> String.join(", ", inputs.stream().map(FixtureTemplate::text).toList()))
                .toList();
    }

    private static List<List<FixtureTemplate>> rowsOfRecord(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model compiles");
        return Adequacy.offeredFor(compilation.db(), OfferingRequest.overTheModule("m"))
                .rowsByBehavior().getOrDefault("record", List.of()).stream()
                .map(row -> row.inputs()).toList();
    }
}
