package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * No object the state of a reading holds has a collection in it that can change, except the ones
 * said here not to.
 *
 * <p>What a reading compares, or leaves alone, is compared by what it holds or as the very object;
 * neither sees a collection inside a record that is added to. The roles say which fields are
 * compared and how, and this asks of the objects in them, for the lookups that go through the
 * readings kept, that none holds a collection which is not immutable.
 *
 * <p>Asked of these models and not of the conformance corpora: the corpora do not go through the
 * readings kept, so a population of them would audit nothing.
 */
class EveryObjectTheStateOfAReadingHoldsIsAsItWasMadeTest {

    /**
     * A lookup of an average over the months a filter keeps, with a guard before it. The readings
     * kept are of the average's form, of the elements the filter and the walk name, and of the
     * comparisons against a path of the input, which is every kind of object the lookups hand to a
     * kept reading; a table of two rows is the least that gives the form more than one number.
     */
    private static final String LOOKUP = """
            module demo

            data Yen = Int
                invariant value >= 0
            data Month = { days: Int, pay: Yen }
            data Window = { first: Month, second: Month }
            data Row = { grade: Int, lowerBound: Yen }
            data Decision = { grade: Int }
            data NoPayable = { nothing: Int }
            let table: List<Row> = [
                Row { grade = 1, lowerBound = Yen(0) },
                Row { grade = 2, lowerBound = Yen(1000) } ]
            let gradeRowFor (m: Yen): Row =
                List.fold((acc, r) -> if r.lowerBound <= m then r else acc,
                          Row { grade = 0, lowerBound = Yen(0) }, table)
            let payableOf (w: Window): List<Month> =
                List.filter(r -> r.days >= 17, [ w.first, w.second ])
            let averageOf (records: List<Month>): Yen =
                Yen(Rational.toInt(DOWN, List.sum(List.map(r -> r.pay.value, records))
                    / List.length(records)))

            behavior f : (w: Window) -> Decision | NoPayable
                constructs Decision, Row, Yen, NoPayable
            let f (w) = {
                let payable = payableOf(w)
                guard List.length(payable) >= 1 else NoPayable { nothing = 0 }
                Decision { grade = gradeRowFor(averageOf(payable)).grade }
            }
            """;

    /** What the report of {@code source} leaves unread, which asks every reading of its rules. */
    private static void readRulesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        ACompiledModel.compiles(compilation);
        AdequacyReport.of(compilation).modules().get(0).behaviors()
                .forEach(each -> each.partition().notRead());
    }

    /**
     * The collections that can change and are not changed, and why. One entry per component, with
     * what it is instead; a component added is a question — is this changed after it is made, and
     * does a reading that compares it see so.
     */
    private static final Map<String, String> NOT_CHANGED = Map.of(
            "souther.compiler.core.Core$Call.args",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.core.Core$Construct.values",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.core.Core$ListLit.elements",
            "the program: a node of the core is made once and read by every phase after",
            "souther.compiler.numeric.LinearForm.coefs",
            "an ordered map of this compiler's, which has no way to put or remove",
            "souther.compiler.inputs.ElementsNamed.named",
            "an ordered map of this compiler's of ordered sets, which have no way to put or remove",
            "souther.compiler.inputs.ElementsNamed.unnamed",
            "an ordered set of this compiler's, which has no way to put or remove",
            "souther.compiler.inputs.TermPath.steps",
            "the steps of a path, an immutable list that works its hash out once");

    @Test
    void theObjectsTheLookupsHoldAreNotChangedInPlace() {
        ReadingState.FOUND.clear();
        ReadingState.auditing = true;
        try {
            readRulesOf(LOOKUP);
        } finally {
            ReadingState.auditing = false;
        }

        Map<String, String> unsaid = new TreeMap<>();
        for (String found : ReadingState.FOUND) {
            String component = found.substring(0, found.indexOf(" is a "));
            if (!NOT_CHANGED.containsKey(component)) {
                unsaid.put(component, found);
            }
        }
        assertEquals(Map.of(), unsaid, "a collection that can change in an object a reading holds");
    }

    @Test
    void aRecordHoldingAListThatCanBeAddedToIsFound() {
        record AHolder(List<String> held) {}
        ReadingState.FOUND.clear();
        ReadingState.auditing = true;
        try {
            class AnOwner {
                final List<AHolder> holders = new ArrayList<>();
            }
            ReadingState reading = new ReadingState(AnOwner.class,
                    Map.of("holders", ReadingRole.INPUT));
            AnOwner owner = new AnOwner();
            owner.holders.add(new AHolder(new ArrayList<>()));
            reading.inputsOf(owner);
        } finally {
            ReadingState.auditing = false;
        }

        assertTrue(ReadingState.FOUND.stream().anyMatch(one -> one.contains("AHolder.held")),
                ReadingState.FOUND.toString());
    }
}
