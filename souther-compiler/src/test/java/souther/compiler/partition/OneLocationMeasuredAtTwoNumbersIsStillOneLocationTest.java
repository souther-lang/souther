package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.BlockedDescent;
import souther.compiler.inputs.TermPath;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.types.Type;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A location measured at two numbers is two measures and one location.
 *
 * <p>Issue #1140 was the first half of that: two numbers of one location came back as neither. The
 * consumers below are the second half. Each of them held a premise that a location carries one
 * measure, and each said something different when it stopped holding — a compiler's own stop
 * reported once per number, and a row written for one class while another class of the same
 * location went unanswered.
 *
 * <p><b>The cells that steer a row are not among them, and the reason is worth writing down.</b>
 * They used to find an axis by the path a condition names, which answers a comparison about the
 * second number with the first number's axis; they ask by the number now. Neither can be told from
 * the other by anything observable, because narrowing an axis of a number taken of a location does
 * not work either way: the class of such an axis recognises what stands at the location, and what
 * it is handed there is the number — so the class holding the line is never found and the condition
 * narrows nothing. That is issue #1144 and is no part of this one.
 */
class OneLocationMeasuredAtTwoNumbersIsStillOneLocationTest {

    private static final String TWO_NUMBERS = """
            module example.two

            data Early
            data Late
            data When = Early | Late

            data Slot = { at: Time }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if Time.hour(slot.at) >= 9 && Time.minute(slot.at) >= 30 then Late else Early
            """;

    /** Two numbers of one location that nothing composes a value for together, which is what the
     *  parts of a time are not. */
    private static final String TWO_QUOTIENTS = """
            module example.two

            data Early
            data Late
            data When = Early | Late

            data Slot = { n: Int }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if slot.n / 2 >= 10 && slot.n / 3 >= 10 then Late else Early
            """;

    /**
     * One position and two measures of it, which is what the rest of this is about.
     *
     * <p>Asserted here so that the three below are about a shape this model actually has. Read as a
     * count of axes alone, every one of them would pass over a model measured at one number.
     */
    @Test
    void theModelHasTwoMeasuresOfOneLocation() {
        Partitions.Partitioning read = partitioningOf();

        assertEquals(List.of(TermPath.of("slot").then("at")),
                read.positions().stream().map(PositionAccount::path).toList());
        assertEquals(List.of("gate/Time.hour(slot.at)", "gate/Time.minute(slot.at)"),
                read.axes().stream().map(each -> each.id().toString()).toList(),
                "in the order the rules were read");
    }

    /**
     * What a reading of a position came to is one entry, however many numbers measure the position.
     *
     * <p>The account of what a measure's reading was short of is one behavior's, and each entry is a
     * thing that went wrong. A stop under a location is one of those — read off the measures, a
     * location measured at two numbers reported this compiler's one stop twice, under two names,
     * and no reader could tell that from two stops.
     *
     * <p>Written against the closure rather than against a source, because a location this compiler
     * cannot enter and that a body measures at two numbers is not a model that can be written today:
     * the operations that take a second number of a location take it of a time or a date, and the
     * walk enters both. What the closure is given is what decides this, so that is what is given.
     */
    @Test
    void oneStopUnderOneLocationIsOneEntryHoweverManyMeasuresStandOnIt() {
        PositionAccount at = new PositionAccount("f", TermPath.of("r").then("cost"), Type.BOOL,
                new ReadingResidue(new BlockedDescent(new BlockReason.ValueRulesNotReached()),
                        java.util.Set.of()),
                souther.compiler.values.ValueSet.ANY, null, List.of(), List.of());

        MeasureClosure.Both closed = MeasureClosure.of(List.of(at), List.of(), new LinesRead());

        assertEquals(List.of(new ClosureGap.PositionNotReachedInto("f", at.id(),
                        new BlockReason.ValueRulesNotReached())),
                List.copyOf(((MeasureClosure.OfThePartition.Open) closed.partition()).by()),
                "the position, once");
    }

    /**
     * And two behaviors measuring positions spelled alike leave two entries.
     *
     * <p>An account of one behavior is put together with another's, and a union keeps one of two
     * equal facts. Told apart by where the position is and nothing else, the second behavior's stop
     * is the first said again — so a module short of two readings reports one.
     */
    @Test
    void oneStopInEachOfTwoBehaviorsIsTwoEntries() {
        souther.compiler.query.WeakeningSet both =
                weakeningOf("f").union(weakeningOf("g"));

        assertEquals(2, both.causes().size(), both.toString());
    }

    private static souther.compiler.query.WeakeningSet weakeningOf(String behavior) {
        PositionAccount at = new PositionAccount(behavior, TermPath.of("r").then("cost"),
                Type.BOOL,
                new ReadingResidue(new BlockedDescent(new BlockReason.ValueRulesNotReached()),
                        java.util.Set.of()),
                souther.compiler.values.ValueSet.ANY, null, List.of(), List.of());
        MeasureClosure.Both closed = MeasureClosure.of(List.of(at), List.of(), new LinesRead());
        return souther.compiler.query.WeakeningSet.of(
                ((MeasureClosure.OfThePartition.Open) closed.partition()).by().stream()
                        .map(souther.compiler.query.Weakening.ModelReadingIncomplete::new)
                        .toArray(souther.compiler.query.Weakening[]::new));
    }

    /**
     * A row for one class of a location stands in every class of it the row is offered as covering.
     *
     * <p>Two measures of one location want a value at it and a row writes one. Each class composed
     * its own, so taking whichever was reached last decided one class while the row was offered as
     * covering both — and the numbers are asked for together instead, which is what one location
     * means.
     *
     * <p>The parts of a time are numbers one value answers at once, and a value answering them is
     * what comes back: the hour below nine and the minute at or above thirty are half past
     * midnight. Where each class was asked on its own, midnight and half past midnight arrived for
     * one location and neither class could be taken.
     */
    @Test
    void twoClassesOfOneLocationAreAnsweredByOneValueStandingInBoth() {
        FillResult filled = filled(TWO_NUMBERS);

        assertEquals(List.of("slot.at=0 <= x < 9", "slot.at=9 <= x <= 23",
                        "slot.at=0 <= x < 30", "slot.at=30 <= x <= 59"),
                filled.rows().stream().flatMap(row -> row.purposes().stream())
                        .flatMap(purpose -> purpose.labels().stream()).toList(),
                "every class of both numbers is answered by a row");
        assertTrue(filled.rows().stream().map(row -> row.inputs().get(0).text())
                        .anyMatch(written -> written.contains("00:30:00")),
                () -> "and the class of the minute is answered by a time whose hour the row's own"
                        + " class of the hour also holds: " + filled.rows());
    }

    /**
     * And where nothing here writes one value for both numbers, no row is written for either class.
     *
     * <p>Two quotients of one whole number are two numbers of one location, and a row writes one
     * value where a location is — so the value is solved for out of both numbers rather than
     * written twice. Each class of each quotient is a run of the place, and a row stands where the
     * runs a pair of them leaves holds a number.
     *
     * <p>The pair that holds none is here beside them. A half below ten is a number below twenty
     * and a third from ten up is a number from thirty up, so that pair of classes is answered by
     * nothing — which is a statement about the model and the reason the rows below are read off the
     * classes they name rather than counted.
     */
    @Test
    void twoClassesOfOneLocationAreAnsweredByOneNumberSolvedOutOfBoth() {
        FillResult filled = filled(TWO_QUOTIENTS);

        assertEquals(List.of("slot.n=10 <= x", "slot.n=x < 10", "slot.n=10 <= x"),
                filled.rows().stream().flatMap(row -> row.purposes().stream())
                        .flatMap(purpose -> purpose.labels().stream()).toList(),
                () -> "a row for every class a number of the place answers: " + filled.rows());
        assertEquals(List.of("Slot { n = 20 }", "Slot { n = 20 }", "Slot { n = 30 }"),
                filled.rows().stream().map(row -> row.inputs().get(0).text()).toList(),
                "and each row's number reads back into the class it was built for: twenty halves"
                        + " to ten and thirds to six, thirty thirds to ten");
    }

    /** The rows a fill of that model's classes comes to. */
    private static FillResult filled(String source) {
        return Generator.fill(MeasuredInput.of("gate", readingOf(source), partitioningOf(source)),
                List.of(), Generator.CandidateCheck.ANY, Budgets.generation());
    }

    /** What the reading of that input says about its numbers, which is what a subject is asked
     *  through. */
    private static souther.compiler.inputs.InputReading readingOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        RuleReadingSource rules = RuleReadings.of(compilation, module);
        return compilation.db().ask(new Adequacy.Inputs(module)).value().get("gate")
                .reading(rules);
    }

    private static Partitions.Partitioning partitioningOf() {
        return partitioningOf(TWO_NUMBERS);
    }

    private static Partitions.Partitioning partitioningOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db()
                .ask(new Adequacy.Divided(compilation.modules().get(0), "gate")).value();
    }
}
