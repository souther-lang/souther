package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.InputReading;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A location whose classes are several numbers of it is asked for a value answering all of them,
 * and what comes back stands in every one or nothing does.
 *
 * <p><b>The sets, and not a number chosen out of each.</b> A class holds a run of numbers and a
 * value is written at one of them, so a search asked for a tuple of chosen numbers answers about
 * that tuple and about nothing else. Where the numbers of a location constrain each other, the
 * difference is the whole answer: the parts of a date do, and a month at or after February with a
 * day at or after the thirtieth is a pair the calendar admits — in March — while the first numbers
 * of those two sets are the thirtieth of February, which is no date at all.
 *
 * <p>So the two are asked here side by side. The exact numbers still answer as they did, because a
 * point of a border is exactly that question; the sets answer about the sets.
 */
class OneValueAnswersEveryClassOfALocationOrNoneDoesTest {

    /** Parts that constrain each other, whose classes leave a pair the calendar admits. */
    private static final String A_MONTH_AND_A_DAY = """
            module example.dated

            data Early
            data Late
            data When = Early | Late

            data Slot = { on: Date }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if Date.month(slot.on) >= 2 && Date.day(slot.on) >= 30 then Late else Early
            """;

    /** The same, with the months cut to February alone, which no thirtieth falls in. */
    private static final String FEBRUARY_AND_A_THIRTIETH = A_MONTH_AND_A_DAY
            .replace("Date.month(slot.on) >= 2 &&",
                    "Date.month(slot.on) >= 2 && Date.month(slot.on) <= 2 &&");

    /**
     * The same, where the months are the ones a rule singled a value out of.
     *
     * <p>A set held as what it excludes rather than as a run, which is the other shape a class of a
     * number comes in. The first month it admits is February, so the pair of first numbers is the
     * thirtieth of February again — and what the sets admit is every other month.
     */
    private static final String ANY_MONTH_BUT_JANUARY = A_MONTH_AND_A_DAY
            .replace("Date.month(slot.on) >= 2", "Date.month(slot.on) /= 1");

    /** Parts that do not constrain each other, which is the pair that worked before. */
    private static final String AN_HOUR_AND_A_MINUTE = """
            module example.dated

            data Early
            data Late
            data When = Early | Late

            data Slot = { at: Time }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if Time.hour(slot.at) >= 9 && Time.minute(slot.at) >= 30 then Late else Early
            """;

    /**
     * A month at or after February with a day at or after the thirtieth is answered by a date.
     *
     * <p>The case the whole of this turns on. Asked at the first number of each set, the answer is
     * that nothing composes one — which is true of the thirtieth of February and says nothing about
     * the classes, since the thirtieth of March stands in both.
     */
    @Test
    void twoClassesOfOneLocationWhoseNumbersConstrainEachOtherAreAnswered() {
        Model model = new Model(A_MONTH_AND_A_DAY);
        TermRealizations.Realization made = model.answering(model.upperClasses());

        List<FixtureTemplate> built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made,
                () -> "a date stands at a month from February on and a day from the thirtieth on: "
                        + made).values();
        assertEquals(List.of("Date(\"2000-03-30\")"),
                built.stream().map(FixtureTemplate::text).toList());
        model.readsBackIntoEveryClass(built, model.upperClasses());
    }

    /**
     * And the same pair of numbers asked for exactly still answers that nothing composes one.
     *
     * <p>Which is the contrast the case above is about rather than a second reading of it. The
     * thirtieth of February is a pair of numbers no date stands at, and a point of a border asking
     * for it is owed that answer — what changed is that a class is not that question.
     */
    @Test
    void theFirstNumberOfEachOfThoseClassesIsAPairNoDateStandsAt() {
        Model model = new Model(A_MONTH_AND_A_DAY);

        assertInstanceOf(TermRealizations.Realization.None.class,
                model.answering(model.at(2, 30)),
                "the thirtieth of February is no date");
    }

    /**
     * And where the classes themselves leave no date, that is what comes back.
     *
     * <p>The other side of the first case, and what keeps it from being a search that says yes to
     * everything. February and the thirtieth are sets the calendar has nothing in, and this may say
     * so because every month and every day the sets admit was tried.
     */
    @Test
    void twoClassesTheCalendarLeavesNothingInAreAnsweredByNothing() {
        Model model = new Model(FEBRUARY_AND_A_THIRTIETH);
        SequencedMap<RealizationTarget, NumericSet> february = model.classesAt(1, 1);

        assertEquals(List.of("2 <= x <= 2", "30 <= x <= 31"), model.labelsAt(1, 1),
                "the months cut to February alone, and the days from the thirtieth on");
        TermRealizations.Realization made = model.answering(february);
        assertInstanceOf(TermRealizations.Realization.None.class, made,
                () -> "no day from the thirtieth on falls in February: " + made);
    }

    /**
     * And a class held as the values it excludes is asked the same way.
     *
     * <p>The other shape a set of numbers comes in, and the reason it is here: such a class carried
     * no number at all, so a location holding one beside another measure was left out of the
     * asking entirely and the two classes went back to offering a value apiece.
     */
    @Test
    void aClassOfEverythingButOneValueIsAskedForTheRestOfThem() {
        Model model = new Model(ANY_MONTH_BUT_JANUARY);
        SequencedMap<RealizationTarget, NumericSet> asked = model.upperClasses();

        assertEquals(List.of("/= 1", "30 <= x <= 31"), model.labelsAt(1, 1),
                "every month but January, and the days from the thirtieth on");
        TermRealizations.Realization made = model.answering(asked);
        List<FixtureTemplate> built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made,
                () -> "a date stands at a month that is not January and a day from the thirtieth"
                        + " on: " + made).values();
        model.readsBackIntoEveryClass(built, asked);

        assertInstanceOf(TermRealizations.Realization.None.class, model.answering(model.at(2, 30)),
                "while the first number each of those admits is the thirtieth of February");
    }

    /**
     * And parts that do not constrain each other are answered as they were.
     *
     * <p>Every hour goes with every minute, so the first number of each set is a time — and the
     * case above is not a general licence to search where there is nothing to search for.
     */
    @Test
    void twoClassesOfOneLocationWhoseNumbersAreIndependentAreAnswered() {
        Model model = new Model(AN_HOUR_AND_A_MINUTE);
        TermRealizations.Realization made = model.answering(model.upperClasses());

        List<FixtureTemplate> built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made,
                () -> "a time stands at an hour from nine on and a minute from thirty on: " + made)
                .values();
        assertEquals(List.of("Time(\"09:30:00\")"),
                built.stream().map(FixtureTemplate::text).toList());
        model.readsBackIntoEveryClass(built, model.upperClasses());
    }

    /** One model, read and divided, with the numbers its classes are of in hand. */
    private static final class Model {

        private final MeasuredInput subject;
        private final Partitions.Partitioning partitioning;

        private Model(String source) {
            Compilation read = Compilation.ofSource(source, "Main");
            read.answerEverything();
            RuleReadingSource rules = RuleReadings.of(read, read.modules().get(0));
            InputReading reading = read.db().ask(new Adequacy.Inputs(read.modules().get(0)))
                    .value().get("gate").reading(rules);

            Compilation divided = Compilation.ofSource(source, "Main");
            divided.measure(Adequacy.Asked.fullReport());
            divided.answerEverything();
            this.partitioning = divided.db()
                    .ask(new Adequacy.Divided(divided.modules().get(0), "gate")).value();
            assertNotNull(partitioning, "the model under test divides its position");
            this.subject = MeasuredInput.of("gate", reading, partitioning);
        }

        /** The uppermost class of each of the location's numbers, which is the one the rules cut
         *  off at the top. */
        private SequencedMap<RealizationTarget, NumericSet> upperClasses() {
            SequencedMap<RealizationTarget, NumericSet> out = new LinkedHashMap<>();
            for (Axis axis : partitioning.axes()) {
                PartitionClass upper = axis.classes().get(axis.classes().size() - 1);
                out.put(RealizationTarget.of(upper.of()), upper.recognises().numbers());
            }
            return out;
        }

        /** One named class of each of the location's numbers, in the order the axes were read. */
        private SequencedMap<RealizationTarget, NumericSet> classesAt(int... which) {
            SequencedMap<RealizationTarget, NumericSet> out = new LinkedHashMap<>();
            List<Axis> axes = partitioning.axes();
            for (int i = 0; i < axes.size() && i < which.length; i++) {
                PartitionClass cls = axes.get(i).classes().get(which[i]);
                out.put(RealizationTarget.of(cls.of()), cls.recognises().numbers());
            }
            return out;
        }

        /** What those classes are called, so a test naming them by where they sit says which they
         *  turned out to be. */
        private List<String> labelsAt(int... which) {
            List<String> out = new ArrayList<>();
            List<Axis> axes = partitioning.axes();
            for (int i = 0; i < axes.size() && i < which.length; i++) {
                out.add(axes.get(i).classes().get(which[i]).label());
            }
            return out;
        }

        /** The same numbers asked for exactly, in the order the axes were read. */
        private SequencedMap<RealizationTarget, NumericSet> at(int... numbers) {
            SequencedMap<RealizationTarget, NumericSet> out = new LinkedHashMap<>();
            List<Axis> axes = partitioning.axes();
            for (int i = 0; i < axes.size() && i < numbers.length; i++) {
                out.put(RealizationTarget.of(axes.get(i).term()),
                        new NumericSet.At(Count.of(BigDecimal.valueOf(numbers[i]))));
            }
            return out;
        }

        /** The number the first axis of this model measures, as something to ask for. */
        private RealizationTarget firstTarget() {
            return RealizationTarget.of(partitioning.axes().get(0).term());
        }

        private TermRealizations.Realization satisfying(RealizationTarget target, NumericSet of) {
            return satisfying(target, of, null);
        }

        private TermRealizations.Realization satisfying(RealizationTarget target, NumericSet of,
                                                        Place named) {
            return TermRealizations.satisfying(
                    subject.inputs().typeAtWrittenPath(target.writeRoot()),
                    subject.quantities().ordersOf(target.term()), of, named,
                    subject.quantities().region(), subject.ruleReading());
        }

        private TermRealizations.Realization answering(
                SequencedMap<RealizationTarget, NumericSet> demands) {
            return TermRealizations.allSatisfying(
                    subject.inputs().typeAtWrittenPath(demands.firstEntry().getKey().writeRoot()),
                    demands, subject.quantities(), subject.quantities().region(),
                    subject.ruleReading());
        }

        /**
         * Every value built reads back as a number each class it was asked for admits.
         *
         * <p>The whole of what a realization owes, asked of the sets rather than of a number: a
         * value that read back somewhere else would be a row offered for classes it does not stand
         * in, which is what a search choosing its own numbers can produce and nothing would catch.
         *
         * <p>The numbers are taken out of what was written and put back to the classes' own answer
         * about membership. Read through the compiler's own reader instead, a reading that agreed
         * with the writing by both being wrong would pass.
         */
        private void readsBackIntoEveryClass(List<FixtureTemplate> built,
                                             SequencedMap<RealizationTarget, NumericSet> asked) {
            List<String> elsewhere = new ArrayList<>();
            for (FixtureTemplate value : built) {
                List<Integer> parts = partsOf(value.text());
                List<NumericSet> sets = new ArrayList<>(asked.values());
                assertEquals(sets.size(), parts.size(),
                        () -> "a part read out of " + value.text() + " for each class asked");
                for (int i = 0; i < sets.size(); i++) {
                    Place read = Count.of(BigDecimal.valueOf(parts.get(i)));
                    if (!sets.get(i).holds(read, carrierOf(asked, i))) {
                        elsewhere.add(value.text() + " reads " + read + " where "
                                + sets.get(i) + " was asked for");
                    }
                }
            }
            assertEquals(List.of(), elsewhere,
                    "every value built reads back as a number the class it was built for admits");
        }

        private souther.compiler.check.Carrier carrierOf(
                SequencedMap<RealizationTarget, NumericSet> asked, int at) {
            return subject.quantities()
                    .ordersOf(new ArrayList<>(asked.keySet()).get(at).term()).answered();
        }

        /** The two parts a rule of these models cuts, in the order the rules were read: the month
         *  and the day of a date, the hour and the minute of a time. */
        private static List<Integer> partsOf(String written) {
            java.util.regex.Matcher date = java.util.regex.Pattern
                    .compile("Date\\(\"(\\d+)-(\\d+)-(\\d+)\"\\)").matcher(written);
            if (date.find()) {
                return List.of(Integer.parseInt(date.group(2)), Integer.parseInt(date.group(3)));
            }
            java.util.regex.Matcher time = java.util.regex.Pattern
                    .compile("Time\\(\"(\\d+):(\\d+):(\\d+)\"\\)").matcher(written);
            assertTrue(time.find(), () -> "a date or a time was written: " + written);
            return List.of(Integer.parseInt(time.group(1)), Integer.parseInt(time.group(2)));
        }
    }
}
