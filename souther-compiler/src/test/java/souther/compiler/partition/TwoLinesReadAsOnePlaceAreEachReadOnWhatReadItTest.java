package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.AnApplicationOfAClosure;
import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two lines read as one place of the author's line are two lines, each read on the applications
 * that read it and on no other.
 *
 * <p>Not made up: a list holding a threshold written out and one chosen between two arms that
 * write it alike is applied a closure that cuts {@code n} at each, and the two are two lines at
 * one place — one held in the data the list holds and one not. The two are taken from that model
 * and told to a reading as two applications' lines: what one application drew is not said of the
 * other because the place is the same.
 */
class TwoLinesReadAsOnePlaceAreEachReadOnWhatReadItTest {

    private static final String MODEL = """
            module g

            data Big = { threshold: Int }
            data Yes
            data No

            behavior classify : (n: Int, c: Bool) -> Yes | No
            let classify (n, c) = {
                    let ks = [ Big { threshold = 100000 }
                             , if c then Big { threshold = 100000 }
                               else Big { threshold = 100000 } ]
                    if List.any((k) -> n >= k.threshold, ks) then Yes else No
                }

            example classify
                | "one" : (1, true) -> No
            """;

    private static ApplicationsReadOn application(int ordinal) {
        ACallOfAnOperation call = new ACallOfAnOperation(
                new ValueName.Stdlib.Operation("List", "any"),
                new ConstructOccurrence(SourceConstructOrigin.written(
                        new WrittenOwner.Body("m", "f"), 1, SourceConstruct.CALL),
                        OccurrenceLineage.ORIGINAL));
        return ApplicationsReadOn.of(List.of(new AnApplicationOfAClosure(List.of(
                AnApplicationOfAClosure.Made.of(call, ordinal).orElseThrow()))));
    }

    @Test
    void twoLinesAtOnePlaceAreEachReadOnWhatReadIt() {
        List<LinesReadOn.DrawnLine> lines = new ArrayList<>(
                ReadComparisons.of(MODEL, "classify").only().readOn().byLine().keySet());
        assertEquals(2, lines.size(), "the model reads two lines: " + lines);
        LinesReadOn.DrawnLine one = lines.get(0);
        LinesReadOn.DrawnLine other = lines.get(1);
        assertEquals(one.place(), other.place(), "at one place: " + lines);

        LinesReadOn.Taking taking = new LinesReadOn.Taking();
        taking.read(one.place(), new Cutting.Read.Cuts(one.cutting(), one.authored()),
                application(0));
        taking.read(other.place(), new Cutting.Read.Cuts(other.cutting(), other.authored()),
                application(1));
        LinesReadOn taken = taking.taken();
        assertEquals(application(0), taken.ofTheLine(one.place(), one.cutting(), one.authored()));
        assertEquals(application(1),
                taken.ofTheLine(other.place(), other.cutting(), other.authored()));
        assertEquals(ApplicationsReadOn.NONE, taken.ofTheComparison(one.cutting(), one.authored()),
                "a comparison not said to come to the line as a whole is no line of it");
    }

    /** One line read on two applications is read on both, and is the comparison's line where
     *  the reading said the comparison came to it as a whole. */
    @Test
    void oneLineReadOnTwoApplicationsIsReadOnBoth() {
        Map<LinesReadOn.DrawnLine, ApplicationsReadOn> told =
                ReadComparisons.of(MODEL, "classify").only().readOn().byLine();
        LinesReadOn.DrawnLine line = told.keySet().iterator().next();
        Cutting.Read read = new Cutting.Read.Cuts(line.cutting(), line.authored());
        LinesReadOn.Taking taking = new LinesReadOn.Taking();
        taking.read(line.place(), read, application(0));
        taking.read(line.place(), read, application(1));
        taking.asAWhole(line.place(), read);
        ApplicationsReadOn both = application(0).and(application(1));
        assertEquals(both, taking.taken().ofTheLine(line.place(), line.cutting(), line.authored()));
        assertEquals(both, taking.taken().ofTheComparison(line.cutting(), line.authored()));
    }
}
