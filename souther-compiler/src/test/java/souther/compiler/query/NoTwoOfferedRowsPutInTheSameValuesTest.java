package souther.compiler.query;

import souther.compiler.check.Sig;
import souther.compiler.execute.BoundaryValues;
import souther.compiler.observe.Comparisons;
import souther.compiler.observe.Limits;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Position;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.ValueTypes;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row offered puts in values no other offered row puts in, and none the author has already
 * written — whether the value is named by a {@code let} or written out.
 *
 * <p>Asked of the values themselves: each input is built by the module's own decoder and two rows
 * are the same when the language says every input of one is the same as the one of the other
 * ({@link Comparisons#same}). Nothing here reads how a row is spelled, so it does not agree with
 * the code under test by sharing its notion of what a row means.
 */
class NoTwoOfferedRowsPutInTheSameValuesTest {

    private static final String SHOTS = """
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

            let nothing: Shot = Hit(0)

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

            """;

    /** The first symptom: the author wrote the row with the name, and it is offered again. */
    private static final String RECORD_BY_NAME = SHOTS + """
            behavior record : (shots: Shots, next: Shot) -> Shots | Closed

            let record (shots, next) =
                if total(shots) >= 50 then Closed else Shots(List.append(shots.value, [next]))

            example record
                | "first" : (Shots([]), nothing) -> Shots([Hit(0)])
            """;

    /** The same row written out. */
    private static final String RECORD_WRITTEN_OUT = RECORD_BY_NAME
            .replace("(Shots([]), nothing)", "(Shots([]), Hit(0))");

    /** The second symptom: the lift is composed on the row that names the value, so the value it
     *  lifts to is the same one written out. The base row has {@code next} first, which is what
     *  puts {@code Miss} in the lifted row. */
    private static final String RECORD_ON_A_NAMED_LIST = SHOTS + """
            let fifty: Shots = Shots([Hit(12), Hit(12), Hit(12), Hit(12), Hit(2)])

            behavior record : (next: Shot, shots: Shots) -> Shots | Closed

            let record (next, shots) =
                if total(shots) >= 50 then Closed else Shots(List.append(shots.value, [next]))

            example total
                | (fifty) -> 50

            example record
                | (Hit(1), fifty) -> Closed
            """;

    @Test
    void aRowWrittenWithTheNameIsNotOfferedAgain() {
        assertNoRepeat(RECORD_BY_NAME);
    }

    @Test
    void aRowWrittenOutIsNotOfferedAgainByTheName() {
        assertNoRepeat(RECORD_WRITTEN_OUT);
    }

    @Test
    void aValueNamedByOneRowAndWrittenOutByALiftIsOfferedOnce() {
        assertNoRepeat(RECORD_ON_A_NAMED_LIST);
    }

    private static void assertNoRepeat(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "the model compiles");
        Db db = compilation.db();
        Sig sig = db.ask(new Bodies.Signatures("m")).value().get("record");
        FixturesAtTheBoundary decoder = Adequacy.constructing(db, "m");
        ValueTypes types = ValueTypes.over(ExampleExecutions.checkedFieldTypes(db));

        List<List<ObservedValue>> offered = new ArrayList<>();
        for (OfferedRow row : Adequacy.offeredFor(db, OfferingRequest.overTheModule("m"))
                .rowsByBehavior().getOrDefault("record", List.of())) {
            List<ObservedValue> values = new ArrayList<>();
            for (int at = 0; at < row.inputs().size(); at++) {
                BoundaryValues.Built built = decoder.build(sig.ins().get(at), row.inputs().get(at));
                assertTrue(built instanceof BoundaryValues.Built.Value,
                        () -> "the offered row builds: " + row.inputs());
                values.add(((BoundaryValues.Built.Value) built).observed());
            }
            offered.add(values);
        }
        assertFalse(offered.isEmpty(), "rows are offered, so there is something to compare");

        List<List<ObservedValue>> written = db.ask(new Output.RowsRead("m")).value()
                .byBehavior().get("record").ran().stream().map(RowOutcome::inputs).toList();
        for (int i = 0; i < offered.size(); i++) {
            for (List<ObservedValue> had : written) {
                int row = i;
                assertFalse(same(had, offered.get(i), sig, types),
                        () -> "offered row " + row + " is a row the author wrote");
            }
            for (int j = i + 1; j < offered.size(); j++) {
                int first = i;
                int second = j;
                assertFalse(same(offered.get(i), offered.get(j), sig, types),
                        () -> "offered rows " + first + " and " + second + " are one row");
            }
        }
    }

    private static boolean same(List<ObservedValue> left, List<ObservedValue> right, Sig sig,
                                ValueTypes types) {
        if (left.size() != right.size()) {
            return false;
        }
        for (int at = 0; at < left.size(); at++) {
            if (Limits.UNBOUNDED.stoppedBy(left.get(at)) != null
                    || Limits.UNBOUNDED.stoppedBy(right.get(at)) != null
                    || !Comparisons.same(left.get(at), right.get(at), types,
                            Position.at(sig.ins().get(at).type()))) {
                return false;
            }
        }
        return true;
    }
}
