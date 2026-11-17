package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.ElementsNamed;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.ModelOccurrences;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.concurrent.atomic.AtomicInteger;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who put an entry on the way is worked out when who put each entry is asked, and not when the
 * entry is made: the entries of a way are asked for far more often than who put them, and a case
 * a line is read in is the one whose entries are asked who put.
 */
class WhoPutAnEntryIsWorkedOutWhenItIsAskedTest {

    private static final ConditionOccurrence CONDITION =
            new ConditionOccurrence("f", ConditionOccurrence.Reading.DIVIDING, 0);

    private static OnTheWay entry() {
        return new OnTheWay.TakenIn(
                new ConditionReportAnchor.WhereTheReadingMetIt("probe", CONDITION),
                new RowDemand.ATruth(TermPath.of("x").then("open"), true),
                NamedElements.of(CONDITION, ElementsNamed.NONE));
    }

    private static ModelOccurrences copy(int ordinal) {
        return ModelOccurrences.of(new ModelOccurrence(SourceConstructOrigin.written(
                new WrittenOwner.Body("probe", "f"), ordinal, SourceConstruct.BINARY),
                ExpansionLineage.ORIGINAL));
    }

    @Test
    void whoPutAnEntryIsNotWorkedOutUntilEachIsAsked() {
        AtomicInteger worked = new AtomicInteger();
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(entry(), () -> {
            worked.incrementAndGet();
            return copy(1);
        });

        assertEquals(0, worked.get(), "the entry is made and nobody asked who put it");
        SaidOnTheWay said = filing.said();

        assertEquals(1, worked.get());
        assertEquals(copy(1), said.entries().get(entry()));
    }

    @Test
    void whatIsWorkedOutIsToldAsWhatIsGivenIs() {
        SaidOnTheWay.Filing given = new SaidOnTheWay.Filing();
        given.alone(entry(), copy(1));
        SaidOnTheWay.Filing late = new SaidOnTheWay.Filing();
        late.alone(entry(), () -> copy(1));

        assertEquals(given.said(), late.said());
    }

    @Test
    void anEntryNothingPutItOnIsNotToldOfAtAll() {
        SaidOnTheWay.Filing filing = new SaidOnTheWay.Filing();
        filing.alone(entry(), () -> ModelOccurrences.NONE);

        assertEquals(SaidOnTheWay.NONE, filing.said());
    }
}
