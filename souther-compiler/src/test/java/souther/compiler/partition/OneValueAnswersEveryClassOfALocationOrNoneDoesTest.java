package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.RowsOfABlock;
import souther.compiler.check.Carrier;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;
import souther.compiler.semantics.TakenAs;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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


    /**
     * Two numbers of one place a value is composed out of: how many a list holds and what it adds
     * up to.
     *
     * <p>Neither is a place in the spelling of a list and neither is read off a value the other
     * asks for — two elements adding up to ten is five and five, and what finds one is filling a
     * container of a size the first number leaves until its elements come to the second.
     */
    private static final String A_LENGTH_AND_A_TOTAL = """
            module example.dated

            data Early
            data Late
            data When = Early | Late

            data Slot = { held: List<Int> }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if List.length(slot.held) >= 2 && List.sum(slot.held) >= 10 then Late else Early
            """;

    /**
     * Two totals of one container, over two paths inside what it holds.
     *
     * <p>A container filled to one total is filled by spreading that total over as many elements as
     * it holds, and there is one spreading. Two totals of one container are two spreadings of one
     * list of elements at once. Totals of fields of their own are composed together; a total of
     * the two fields together beside the total of one of them is a group this writes none of.
     */
    private static final String TWO_TOTALS_OF_ONE_CONTAINER = """
            module example.totals

            data Early
            data Late
            data When = Early | Late

            data Line = { a: Int, b: Int }
            data Slot = { held: List<Line> }

            behavior gate : (slot: Slot) -> When
            let gate (slot) =
                if List.sum(List.map(l -> l.a, slot.held)) >= 10
                    && List.sum(List.map(l -> l.b, slot.held)) >= 20 then Late else Early
            """;

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
        SequencedMap<RealizationTarget.OfANumber, NumericSet> february = model.classesAt(1, 1);

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
        SequencedMap<RealizationTarget.OfANumber, NumericSet> asked = model.upperClasses();

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

    /**
     * And a group nothing here solves a value out of says that, and not that no value answers it.
     *
     * <p>How many a list holds and what it adds up to are two numbers of one place that nothing
     * here solves a value out of — the quotients above are solved for, and these are not. Nothing
     * walked anything before the answer came back, so an answer in the words of a walk that looked
     * everywhere is a statement about the model made by a reader with no standing to make one.
     * What it says instead is which population this compiler writes none of.
     */
    @Test
    void aContainerIsComposedOutOfHowManyItHoldsAndWhatItComesTo() {
        Model model = new Model(A_LENGTH_AND_A_TOTAL);
        SequencedMap<RealizationTarget.OfANumber, NumericSet> asked = model.upperClasses();

        assertEquals(2, asked.size(), () -> "a length and a total of one place: " + asked.keySet());
        TermRealizations.Realization made = model.answering(asked);
        TermRealizations.Realization.Built built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made,
                () -> "a container holding that many and coming to that is composed: " + made);
        model.aContainerReadsBackIntoBothClasses(built.values(), asked);
    }

    /**
     * And a group nothing here composes a value for says that, and not that no value answers it.
     *
     * <p>Two totals of one container are two spreadings of one list of elements, which is neither
     * the composing above nor a number read off what it composed. Nothing walked anything before
     * the answer came back, so an answer in the words of a walk that looked everywhere is a
     * statement about the model made by a reader with no standing to make one. What it says instead
     * is which population this compiler writes none of.
     */
    @Test
    void aGroupNothingComposesAValueForIsSaidAsThePopulationAndNotAsNothing() {
        Model model = new Model(TWO_TOTALS_OF_ONE_CONTAINER);

        TermRealizations.JointRealization way = TermRealizations.jointRealizationOf(
                List.of(model.aTotalOver("a"), model.aTotalOverBothFields()));

        TermRealizations.JointRealization.Missing missing = assertInstanceOf(
                TermRealizations.JointRealization.Missing.class, way,
                () -> "nothing here composes a value out of both totals: " + way);
        assertEquals(CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS,
                missing.notAllOf(), "and says which population it wrote none of");
    }

    /**
     * And the way that comes back is a way for every number of the group, never for some of them.
     *
     * <p>The value of a container beside a total taken over what it holds is one location asked for
     * two numbers, and the values the first admits are not read for the second — nothing here reads
     * a number of a run off one value. A way for the first alone would be a builder that answers
     * what half the group asked and is offered as the answer to all of it, and the row would stand
     * at a class of the total nothing put it in.
     */
    @Test
    void aWayForSomeOfAGroupIsNotOfferedAsAWayForTheGroup() {
        Model model = new Model(TWO_TOTALS_OF_ONE_CONTAINER);

        assertInstanceOf(TermRealizations.JointRealization.Missing.class,
                TermRealizations.jointRealizationOf(
                        List.of(model.theContainerItself(), model.aTotalOver("a"))),
                "the value of the container and a total over what it holds");
    }

    /**
     * And a group the arm owns part of is not the arm's either.
     *
     * <p>Beside the one above and not a shape of it: there the arm holds one number of two, here it
     * holds two of three and what is built for them would be offered as a value for all three. A
     * way chosen by what it recognises rather than by what the group is would take this one, and
     * the number it never saw is the one the row is put at a class of.
     */
    @Test
    void aWayForMostOfAGroupIsNotOfferedEither() {
        Model model = new Model(TWO_TOTALS_OF_ONE_CONTAINER);

        assertInstanceOf(TermRealizations.JointRealization.Missing.class,
                TermRealizations.jointRealizationOf(List.of(model.theContainerItself(),
                        model.howManyItHolds(), model.aTotalOver("a"))),
                "the value of the container, how many it holds and a total over what it holds");
    }

    /**
     * A string held to three values, divided by the values themselves and by how long each is.
     *
     * <p>{@code " a"} and {@code "bb"} are two long and {@code "c"} is one, so a class of the value
     * and a class of the length are in one value exactly where the value is that long.
     */
    private static final String THREE_STRINGS = """
            module example.named

            data Ok
            data No
            data Verdict = Ok | No
            data Code = String
                invariant value == " a" || value == "bb" || value == "c"

            behavior gate : (c: Code) -> Verdict
            let gate (c) = if String.length(c.value) == 2
                && String.length(String.trim(c.value)) == 1 then No else Ok
            """;

    /**
     * A class of the value and a class of a number taken of it are answered by a value that is in
     * both.
     *
     * <p>Each class composed a value for itself, so the value {@code " a"} and the lengths of two
     * — {@code " a"} and {@code "bb"} — were two writes of one location, and the row was refused
     * as one holding two values at once.
     */
    @Test
    void aClassOfTheValueAndAClassOfANumberTakenOfItAreAnsweredByOneValue() {
        Model model = new Model(THREE_STRINGS);
        TermRealizations.Realization made = model.answering(model.classesLabelled("\" a\"", "= 2"));

        List<FixtureTemplate> built = assertInstanceOf(
                TermRealizations.Realization.Built.class, made, made::toString).values();
        assertEquals(List.of("Code(\" a\")"), built.stream().map(FixtureTemplate::text).toList());
    }

    /**
     * And where no value named is in both, that is what the model settles: every value the
     * position can hold was read through both, and none is {@code "c"} and two long.
     */
    @Test
    void aClassOfTheValueAndAClassOfANumberNoValueIsInAreAnsweredAsNoValue() {
        Model model = new Model(THREE_STRINGS);
        TermRealizations.Realization made = model.answering(model.classesLabelled("\"c\"", "= 2"));

        TermRealizations.Realization.None none = assertInstanceOf(
                TermRealizations.Realization.None.class, made, made::toString);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE, none.why());
    }

    /**
     * And a number picked out of a class to try is answered about that number alone: a caller that
     * picked one length out of every length but two has asked whether one value stands there,
     * which is no statement about the lengths it was picked out of.
     *
     * <p>The same two classes asked whole are what the model settles, as above: {@code " a"} is
     * two long and in no length but two.
     */
    @Test
    void aNumberPickedOutOfAClassToTryIsAnsweredAboutThatNumberAlone() {
        Model model = new Model(THREE_STRINGS);
        SequencedMap<RealizationTarget.OfANumber, NumericSet> classes =
                model.classesLabelled("\" a\"", "/= 2");
        TermRealizations.Realization whole = model.answering(classes);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE,
                assertInstanceOf(TermRealizations.Realization.None.class, whole,
                        whole::toString).why());

        SequencedMap<RealizationTarget, AskedAt> asked = new LinkedHashMap<>();
        classes.forEach((target, admits) -> {
            Carrier on = model.subject.quantities().ordersOf(target.term()).answered();
            asked.put(target, target.term() instanceof NumericTerm.ValueOf
                    ? AskedAt.theClass(admits, on)
                    : AskedAt.aNumberOutOf(admits, Count.of(BigDecimal.ONE), on));
        });
        TermRealizations.Realization picked = model.answeringAsked(asked);
        assertEquals(Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE,
                assertInstanceOf(TermRealizations.Realization.None.class, picked,
                        picked::toString).why());
    }

    /**
     * And the rows a reader is handed: every class of the length is written with a value of it,
     * and none is said to need the value to be two things.
     */
    @Test
    void theRowsForTheClassesOfTheLengthAreWrittenWithAValueOfEach() {
        Compilation compilation = Compilation.ofSource(THREE_STRINGS, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String rows = GeneratedRows.of(compilation, "example.named", "gate",
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();

        assertFalse(rows.contains("would have to hold two values at once"), rows);
        assertFalse(rows.contains("no row for"), rows);
        assertTrue(RowsOfABlock.of(rows).stream().anyMatch(row -> row.isFor("c== 2")), rows);
        assertTrue(RowsOfABlock.of(rows).stream().anyMatch(row -> row.isFor("c=/= 2")), rows);
    }

    /** A whole number held to three values, divided by what it leaves by two, three and five. */
    private static final String THREE_REMAINDERS = """
            module example.named

            data Ok
            data No
            data Verdict = Ok | No
            data Code = Int
                invariant value == 7 || value == 11 || value == 16

            behavior gate : (c: Code) -> Verdict
            let gate (c) = if Int.floorMod(c.value, 2) == 1 && Int.floorMod(c.value, 3) == 1
                && Int.floorMod(c.value, 5) == 1 then No else Ok
            """;

    /**
     * Three classes no one value is in, though every two of them are.
     *
     * <p>Seven leaves one by two and three, eleven by two and five, sixteen by three and five, and
     * none of them by all three. So a group is answered by what one value reads as of every number
     * at once, and not by the pairs: each pair is in some value, and the three are in none.
     */
    @Test
    void threeClassesEveryTwoOfWhichOneValueIsInAreAnsweredByNoValue() {
        Model model = new Model(THREE_REMAINDERS);
        List<SequencedMap<RealizationTarget.OfANumber, NumericSet>> each =
                model.classOfEachTakenNumberLabelled("= 1");
        assertEquals(3, each.size(), each::toString);

        for (int left = 0; left < each.size(); left++) {
            SequencedMap<RealizationTarget.OfANumber, NumericSet> pair = new LinkedHashMap<>();
            for (int i = 0; i < each.size(); i++) {
                if (i != left) {
                    pair.putAll(each.get(i));
                }
            }
            TermRealizations.Realization made = model.answering(pair);
            assertInstanceOf(TermRealizations.Realization.Built.class, made, made::toString);
        }
        SequencedMap<RealizationTarget.OfANumber, NumericSet> all = new LinkedHashMap<>();
        each.forEach(all::putAll);
        TermRealizations.Realization made = model.answering(all);
        assertEquals(Generator.UnresolvedCombination.Reason.NO_VALUE_CAN_STAND_THERE,
                assertInstanceOf(TermRealizations.Realization.None.class, made, made::toString)
                        .why());
    }

    /**
     * A rule telling sets of values apart, on a position whose declarations name its values, leaves
     * the position divided at the values named — so the class of the value is a value at a place,
     * and is composed with a class of a number taken of it as one value.
     *
     * <p>The premise the composing rests on, held here rather than said. A rule of sets makes classes
     * that are sets ({@code Classing}), and a set has no number for the composing to read; what
     * keeps those classes off such a position is that the declarations already divide it, at the
     * values they name, and a body's rules only ever refine that ({@code Partitions.classesOf}).
     * Wherever the values are named — on the value's own type, on a record holding it, on the
     * element of a container.
     */
    @Test
    void aRuleOfSetsOnAPositionWhoseValuesAreNamedLeavesItDividedAtThoseValues() {
        String verdict = """
                module example.named

                data Ok
                data No
                data Verdict = Ok | No
                """;
        String rule = "String.startsWith(\"a\", %1$s) && String.length(%1$s) == 2";
        List<String> models = List.of(verdict + """
                data Code = String
                    invariant value == "aa" || value == "bb" || value == "c"

                behavior gate : (c: Code) -> Verdict
                let gate (c) = if %s then No else Ok
                """.formatted(rule.formatted("c.value")), verdict + """
                data Request = { code: String }
                    invariant code == "aa" || code == "bb" || code == "c"

                behavior gate : (r: Request) -> Verdict
                let gate (r) = if %s then No else Ok
                """.formatted(rule.formatted("r.code")), verdict + """
                data Code = String
                    invariant value == "aa" || value == "bb" || value == "c"
                data Request = { codes: List<Code> }

                behavior gate : (r: Request) -> Verdict
                let gate (r) = if List.any(c -> %s, r.codes) then No else Ok
                """.formatted(rule.formatted("c.value")));
        for (String source : models) {
            Model model = new Model(source);
            List<String> ofTheValue = new ArrayList<>();
            for (Axis axis : model.partitioning.axes()) {
                if (!(axis.term() instanceof NumericTerm.ValueOf)) {
                    continue;
                }
                for (PartitionClass cls : axis.classes()) {
                    assertInstanceOf(NumericSet.At.class, cls.recognises().numbers(),
                            () -> "a class of the value is a value at a place: " + cls);
                    ofTheValue.add(cls.label());
                }
            }
            assertEquals(List.of("\"aa\"", "\"bb\"", "\"c\""), ofTheValue, source);

            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String rows = GeneratedRows.of(compilation, "example.named", "gate",
                    SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
            assertFalse(rows.contains("would have to hold two values at once"), rows);
        }
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
        private SequencedMap<RealizationTarget.OfANumber, NumericSet> upperClasses() {
            SequencedMap<RealizationTarget.OfANumber, NumericSet> out = new LinkedHashMap<>();
            for (Axis axis : partitioning.axes()) {
                PartitionClass upper = axis.classes().get(axis.classes().size() - 1);
                out.put(RealizationTarget.of(upper.of()), upper.recognises().numbers());
            }
            return out;
        }

        /** One named class of each of the location's numbers, in the order the axes were read. */
        private SequencedMap<RealizationTarget.OfANumber, NumericSet> classesAt(int... which) {
            SequencedMap<RealizationTarget.OfANumber, NumericSet> out = new LinkedHashMap<>();
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
        private SequencedMap<RealizationTarget.OfANumber, NumericSet> at(int... numbers) {
            SequencedMap<RealizationTarget.OfANumber, NumericSet> out = new LinkedHashMap<>();
            List<Axis> axes = partitioning.axes();
            for (int i = 0; i < axes.size() && i < numbers.length; i++) {
                out.put(RealizationTarget.of(axes.get(i).term()),
                        new NumericSet.At(Count.of(BigDecimal.valueOf(numbers[i]))));
            }
            return out;
        }

        /** The classes called {@code labels}, one of each, whichever of the location's numbers
         *  each is a class of. */
        private SequencedMap<RealizationTarget.OfANumber, NumericSet> classesLabelled(
                String... labels) {
            SequencedMap<RealizationTarget.OfANumber, NumericSet> out = new LinkedHashMap<>();
            for (String label : labels) {
                PartitionClass cls = partitioning.axes().stream()
                        .flatMap(axis -> axis.classes().stream())
                        .filter(each -> each.label().equals(label)).findFirst()
                        .orElseThrow(() -> new AssertionError("no class " + label + " among "
                                + partitioning.axes().stream().flatMap(axis -> axis.classes()
                                        .stream()).map(PartitionClass::label).toList()));
                out.put(RealizationTarget.of(cls.of()), cls.recognises().numbers());
            }
            return out;
        }

        /** The class called {@code label} of each number taken of the location, one map apiece,
         *  in the order the axes were read. */
        private List<SequencedMap<RealizationTarget.OfANumber, NumericSet>>
                classOfEachTakenNumberLabelled(String label) {
            List<SequencedMap<RealizationTarget.OfANumber, NumericSet>> out = new ArrayList<>();
            for (Axis axis : partitioning.axes()) {
                if (axis.term() instanceof NumericTerm.ValueOf) {
                    continue;
                }
                for (PartitionClass cls : axis.classes()) {
                    if (cls.label().equals(label)) {
                        SequencedMap<RealizationTarget.OfANumber, NumericSet> one =
                                new LinkedHashMap<>();
                        one.put(RealizationTarget.of(cls.of()), cls.recognises().numbers());
                        out.add(one);
                    }
                }
            }
            return out;
        }

        private TermRealizations.Realization answering(
                SequencedMap<RealizationTarget.OfANumber, NumericSet> demands) {
            // The classes as they are asked for, which is what a search of one is about: these
            // fixtures hand over what a rule leaves and nothing picked a number out of it.
            SequencedMap<RealizationTarget, AskedAt> asked = new LinkedHashMap<>();
            demands.forEach((target, admits) -> asked.put(target, AskedAt.theClass(admits,
                    subject.quantities().ordersOf(target.term()).answered())));
            return answeringAsked(asked);
        }

        private TermRealizations.Realization answeringAsked(
                SequencedMap<RealizationTarget, AskedAt> asked) {
            return TermRealizations.allSatisfying(
                    subject.inputs().typeAtWrittenPath(asked.firstEntry().getKey().writeRoot()),
                    asked, subject.quantities(), subject.quantities().region(),
                    subject.ruleReading());
        }

        /** The value the container itself stands at, which is one number of its location. */
        private RealizationTarget theContainerItself() {
            return RealizationTarget.of(new NumericTerm.ValueOf(theContainer()));
        }

        /** How many that container holds, which is a number read off the value standing there. */
        private RealizationTarget howManyItHolds() {
            NumericTerm.TakenOf many = NumericTerm.TakenOf.asItStands(
                    ValueName.Stdlib.operation("List", "length"), theContainer(),
                    subject.inputs().typeAtWrittenPath(theContainer()),
                    subject.ruleReading().source().inners(),
                    subject.ruleReading().source().symbols());
            assertNotNull(many, "how many a list holds is a number taken of the list");
            return RealizationTarget.of(many);
        }

        private static TermPath theContainer() {
            return TermPath.of("slot").then("held");
        }

        /**
         * The total of what stands at {@code field} in each element of the container, named here
         * rather than read off a rule.
         *
         * <p>No rule of the model draws a line on one of these, and what is under test is the
         * classification rather than which rules reach it. Built through the one way a term of a
         * run is made, so the account is the operation's own answer and not this test's.
         */
        private RealizationTarget aTotalOver(String field) {
            TermPath each = TermPath.of("slot").then("held").element().then(field);
            NumericTerm.TakenOver over = NumericTerm.TakenOver.of(
                    ValueName.Stdlib.operation("List", "sum"),
                    RunSource.overTheOccurrencesAt(each), Type.INT,
                    subject.ruleReading().source().inners(),
                    subject.ruleReading().source().symbols());
            assertNotNull(over, "a total over the occurrences of a path is a number of the run");
            return RealizationTarget.of(over);
        }

        /**
         * What the elements come to when each is counted as its two fields together, which is a
         * total of no one field of them.
         */
        private RealizationTarget aTotalOverBothFields() {
            TermPath elements = TermPath.of("slot").then("held").element();
            NumericTerm.TakenOver over = NumericTerm.TakenOver.of(
                    ValueName.Stdlib.operation("List", "sum"),
                    new RunSource.ComputedOccurrences(elements, new ElementValue.Affine(
                            new LinearForm<>(ExactRatio.ZERO, Map.of(
                                    ElementProjection.ofFields(List.of("a")), ExactRatio.ONE,
                                    ElementProjection.ofFields(List.of("b")), ExactRatio.ONE))),
                            Type.INT, null),
                    Type.INT, subject.ruleReading().source().inners(),
                    subject.ruleReading().source().symbols());
            assertNotNull(over, "a total over what is computed of each element is a number of a run");
            return RealizationTarget.of(over);
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
                                             SequencedMap<RealizationTarget.OfANumber, NumericSet> asked) {
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

        /**
         * Every container built holds as many as one class asked for and comes to a number the
         * other asked for.
         *
         * <p>Read out of what was written and put back to each class's own answer about
         * membership, the way the other two read-backs here are: the elements are counted and
         * added up out of the text, so a container that was composed against one of the two
         * numbers and offered for both does not pass.
         */
        private void aContainerReadsBackIntoBothClasses(
                List<FixtureTemplate> built, SequencedMap<RealizationTarget.OfANumber, NumericSet> asked) {
            List<String> elsewhere = new ArrayList<>();
            for (FixtureTemplate value : built) {
                List<BigDecimal> held = elementsOf(value.text());
                BigDecimal total = held.stream().reduce(BigDecimal.ZERO, BigDecimal::add);
                int i = 0;
                for (Map.Entry<RealizationTarget.OfANumber, NumericSet> each : asked.entrySet()) {
                    TakenAs how = ((NumericTerm.TakenOf) each.getKey().term()).takenAs();
                    Place read = how instanceof TakenAs.HowManyItHolds
                            ? Count.of(BigDecimal.valueOf(held.size())) : Count.of(total);
                    if (!each.getValue().holds(read, carrierOf(asked, i))) {
                        elsewhere.add(value.text() + " reads " + read + " where "
                                + each.getValue() + " was asked for");
                    }
                    i++;
                }
            }
            assertEquals(List.of(), elsewhere,
                    "every container built holds as many and comes to as much as was asked for");
        }

        /** The numbers a written container holds, in the order it holds them. */
        private static List<BigDecimal> elementsOf(String written) {
            List<BigDecimal> out = new ArrayList<>();
            java.util.regex.Matcher each = java.util.regex.Pattern
                    .compile("-?\\d+(\\.\\d+)?").matcher(written);
            while (each.find()) {
                out.add(new BigDecimal(each.group()));
            }
            return out;
        }

        private souther.compiler.check.Carrier carrierOf(
                SequencedMap<RealizationTarget.OfANumber, NumericSet> asked, int at) {
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
