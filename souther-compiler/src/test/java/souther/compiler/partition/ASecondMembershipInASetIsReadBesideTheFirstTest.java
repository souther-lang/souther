package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two memberships in one set are two elements of it. What the first asks of the set is met by an
 * element apart from the one the second reads, wherever the set is held to more than one element,
 * so the second relation is read as it is beside nothing: the value it relates to the set's
 * elements and the elements themselves are left over every value.
 *
 * <p>The same for an {@code Int} and a date, whose ends do not make the first membership say
 * anything of the second: the element is written at the same value, which its type holds wherever
 * the value is, and a set of dates holds as many dates as a set of numbers.
 */
class ASecondMembershipInASetIsReadBesideTheFirstTest {

    /** The places what {@code f} states is not read of, as the findings the report is written
     *  from say them: a rule whose reading stopped, and not one read to the end that draws no
     *  line, which the report says apart. */
    private static List<String> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return compilation.db().ask(new Adequacy.Coverage("demo")).value().get("f").notRead()
                .stream()
                .filter(each -> !(each instanceof PartitionEvidence.NotRead.ARule)
                        || each.readingStopped())
                .map(PartitionEvidence.NotRead::at).sorted().toList();
    }

    private static String ofNumbers(String body) {
        return """
                module demo

                behavior f : (hs: Set<Int>, a: Int) -> Bool

                let f (hs, a) = %s
                """.formatted(body);
    }

    private static String ofDates(String body) {
        return """
                module demo

                behavior f : (holidays: Set<Date>, from: Date) -> Bool

                let f (holidays, from) = %s
                """.formatted(body);
    }

    /** The first membership holds: some element is the number, and another is asked for. */
    @Test
    void aMembershipAfterOneThatHoldsIsReadOverEveryNumber() {
        assertEquals(List.of(), unread(ofNumbers(
                "Set.contains(a, hs) && Set.contains(a + 1, hs)")));
    }

    /** The first fails: every element is another number than the one asked after it. */
    @Test
    void aMembershipAfterOneThatFailsIsReadOverEveryNumber() {
        assertEquals(List.of(), unread(ofNumbers(
                "Set.contains(a, hs) || Set.contains(a + 1, hs)")));
        assertEquals(List.of(), unread(ofNumbers(
                "Bool.not(Set.contains(a, hs)) && Set.contains(a + 1, hs)")));
    }

    @Test
    void aMembershipAfterOneThatHoldsIsReadOverEveryDate() {
        assertEquals(List.of(), unread(ofDates(
                "Set.contains(from, holidays) && Set.contains(Date.addDays(1, from), holidays)")));
    }

    @Test
    void aMembershipAfterOneThatFailsIsReadOverEveryDate() {
        assertEquals(List.of(), unread(ofDates(
                "Set.contains(from, holidays) || Set.contains(Date.addDays(1, from), holidays)")));
        assertEquals(List.of(), unread(ofDates(
                "Bool.not(Set.contains(from, holidays))"
                        + " && Set.contains(Date.addDays(1, from), holidays)")));
    }

    /**
     * A set a rule holds to one element is not two elements: the first membership taking the
     * element, no row asks the second of another, and the reading does not claim one.
     */
    @Test
    void aSetHeldToOneElementIsNotTakenForTwo() {
        assertEquals(List.of("bag.a", "bag.hs[*]"), unread("""
                module demo

                data Bag = { hs: Set<Int>, a: Int } invariant Set.size(hs) <= 1

                behavior f : (bag: Bag) -> Bool

                let f (bag) = Set.contains(bag.a, bag.hs) && Set.contains(bag.a + 1, bag.hs)
                """));
    }
}
