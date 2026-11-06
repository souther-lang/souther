package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.AnApplicationOfAClosure;
import souther.compiler.types.ApplicationsReadOn;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * Where two applications read the place of one of the author's lines as two different lines, the
 * place says nothing of which read which, and a line read as it is read on none; where they read
 * it as one line, the line is read on both.
 *
 * <p>Not made up: a list holding a threshold written out and one chosen between two arms that
 * write it alike is applied a closure that cuts {@code n} at each, and the two are two lines at
 * one place — one held in the data the list holds and one not. Put together under the place, each
 * would be read on the application of the other.
 */
class APlaceReadAsTwoLinesIsReadOnNoApplicationTest {

    private static final PlaceOfALine PLACE = new PlaceOfALine(
            PartOfAComparison.of(WrittenLine.THE_COMPARISON), Spelling.of("n >= 100000"));

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
    void twoLinesAtOnePlaceAreReadOnNoneAndOneLineIsReadOnBoth() {
        Cutting.Read one = new Cutting.Read.CutsNothing(List.of());
        Cutting.Read other = new Cutting.Read.StatesNoRelation();

        LinesReadOn.Taking two = new LinesReadOn.Taking();
        two.read(PLACE, one, application(0));
        two.read(PLACE, other, application(1));
        two.asAWhole(PLACE);
        assertEquals(Set.of(PLACE), two.taken().notToldApart());
        assertEquals(ApplicationsReadOn.NONE, two.taken().ofTheLine(PLACE));
        assertEquals(ApplicationsReadOn.NONE, two.taken().ofTheComparison());

        LinesReadOn.Taking alike = new LinesReadOn.Taking();
        alike.read(PLACE, one, application(0));
        alike.read(PLACE, one, application(1));
        assertEquals(application(0).and(application(1)), alike.taken().ofTheLine(PLACE));
        assertEquals(ApplicationsReadOn.NONE, alike.taken().ofTheComparison(),
                "a comparison not said to come to the line as a whole is no line of it");
        alike.asAWhole(PLACE);
        assertEquals(application(0).and(application(1)), alike.taken().ofTheComparison());
    }

    @Test
    void aModelReadsOnePlaceAsTwoLines() {
        LinesReadOn readOn = ReadComparisons.of("""
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
                """, "classify").only().readOn();
        assertFalse(readOn.notToldApart().isEmpty(), readOn.toString());
        readOn.notToldApart().forEach(place ->
                assertEquals(ApplicationsReadOn.NONE, readOn.ofTheLine(place)));
    }
}
