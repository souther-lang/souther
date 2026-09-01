package souther.program.api;

import souther.compiler.observe.Verdict;
import souther.compiler.program.CheckedBehavior;
import souther.compiler.program.CheckedModule;
import souther.compiler.program.CheckedProgram;
import souther.compiler.program.CheckedRow;
import souther.compiler.program.StandsIn;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A stand-in answers an output what it answered the run.
 *
 * <p>Which row of a fake's table answers a call is decided twice: by the run this compile made, out
 * of the values it built, and by an output holding the row, out of the values it was handed. The two
 * are different code — one compares what a class loader built and the other what an observation
 * carries — and where they part, a row that held here is a row the output's run of it fails, with
 * nothing about either saying why.
 *
 * <p>Held to each other through the rows. Each behavior below hands its input straight to what it
 * depends on and answers what that answers, so what the row states of the answer is what the fake
 * answered when the row ran — and the program was accepted, which is this compile saying the row
 * held. Asking the stand-in the same question and holding the row to what it says puts the two
 * dispatches on one row: the same table, the same arguments, and one answer they both have to give.
 */
class AStandInAnswersWhatItAnsweredWhenTheRowRanTest {

    private static final String MODULE = """
            module demo

            data Price = Int
            data Rate = Int
            data Tags = { of: Set<Int> }
            data Label = String

            behavior rateFor : (of: Price) -> Rate

            behavior rateOf : (base: Price) -> Rate
                depends on rateFor

            let rateOf (base, rateFor) = rateFor(base)

            behavior labelFor : (tags: Tags) -> Label

            behavior labelOf : (tags: Tags) -> Label
                depends on labelFor

            let labelOf (tags, labelFor) = labelFor(tags)

            fake rateFor
                | (Price(1)) -> Rate(10)
                | (Price(2)) -> Rate(20)
                | _ -> Rate(99)

            fake labelFor
                | (Tags { of = [ 1, 2 ] }) -> Label("both")

            example rateOf
                | "a price the table lists" : (Price(1)) -> Rate(10)
                | "another price it lists" : (Price(2)) -> Rate(20)
                | "a price it does not list" : (Price(7)) -> Rate(99)

            example labelOf
                | "the same set in another order" : (Tags { of = [ 2, 1 ] }) -> Label("both")
            """;

    /**
     * Every row of a behavior that passes its input on holds against what its stand-in answers.
     *
     * <p>Over all four, so that the row the table lists, the row nothing lists, and the row whose
     * argument is the same set written in another order are each one the two dispatches agree on.
     */
    @Test
    void whatAStandInAnswersIsWhatTheRowWasHeldAgainst() {
        CheckedProgram program = CheckedProgram.of(List.of(MODULE));

        List<String> asked = new ArrayList<>();
        for (CheckedRow row : rowsOf(program)) {
            CheckedRow.WithStandIns states =
                    assertInstanceOf(CheckedRow.WithStandIns.class, row.statement(),
                            () -> row + " is a row of a behavior that depends on something");
            StandsIn standsIn = states.standsIn().get(0);
            StandsIn.Answer answered = standsIn.answering(states.states().inputs());

            StandsIn.Answer.TheValue value = assertInstanceOf(StandsIn.Answer.TheValue.class,
                    answered, () -> standsIn + " answered nothing for " + row);
            assertEquals(new Verdict.Held(), states.holds(value.value()),
                    () -> "what " + standsIn + " answers for " + row + " is not what the row was"
                            + " held against when it ran");
            asked.add(row.identity().shown());
        }

        assertEquals(List.of("a price the table lists", "another price it lists",
                        "a price it does not list", "the same set in another order"), asked,
                "every row of a behavior that passes its input on");
    }

    /**
     * A table asked something it does not list, and does not answer for, states no answer.
     *
     * <p>The table's own rule and not the reader's. A stand-in that answered anything here would
     * have an output run the row against a value nobody wrote; one that could not be asked would
     * have the output decide for itself what an unlisted argument means.
     */
    @Test
    void aTableWithNoDefaultStatesNoAnswerForWhatItDoesNotList() {
        CheckedProgram program = CheckedProgram.of(List.of("""
                module demo

                data Price = Int
                data Rate = Int

                behavior rateFor : (of: Price) -> Rate

                behavior rateOf : (base: Price) -> Rate
                    depends on rateFor

                let rateOf (base, rateFor) = rateFor(base)

                fake rateFor
                    | (Price(1)) -> Rate(10)

                example rateOf
                    | "the one price it lists" : (Price(1)) -> Rate(10)
                """));

        CheckedRow row = behavior(program, "rateOf").rows().get(0);
        StandsIn standsIn = assertInstanceOf(CheckedRow.WithStandIns.class, row.statement())
                .standsIn().get(0);

        assertEquals(new StandsIn.Answer.NothingStated(),
                standsIn.answering(List.of(price(2))),
                "the table lists one price and answers nothing for the rest");
    }

    /**
     * A {@code with} and a table that lists nothing cross as one thing.
     *
     * <p>The two are one thing to a reader — what this dependency answers — and which of them was
     * written is a fact about the text. Crossing as two, an output would have two ways to ask one
     * question, and would answer for itself what a `with` does with an argument it was not written
     * for.
     */
    @Test
    void aWithAndATableThatListsNothingCrossAsOneThing() {
        String written = """
                module demo

                data Price = Int
                data Rate = Int

                behavior rateFor : (of: Price) -> Rate

                behavior rateOf : (base: Price) -> Rate
                    depends on rateFor

                let rateOf (base, rateFor) = rateFor(base)

                %s
                """;

        StandsIn onTheRow = onlyStandIn(String.format(written, """
                example rateOf
                    | "on the row" : (Price(1)) with rateFor = Rate(10) -> Rate(10)
                """));
        StandsIn inATable = onlyStandIn(String.format(written, """
                fake rateFor
                    | _ -> Rate(10)

                example rateOf
                    | "in a table" : (Price(1)) -> Rate(10)
                """));

        assertEquals(List.of(), onTheRow.stated().entries(),
                "a `with` lists nothing: it answers the same whatever it is asked");
        assertEquals(List.of(), inATable.stated().entries(),
                "and neither does a table written with only a default");
        // Asked the same, they answer the same — for an argument neither of them was written
        // against as much as for one either was.
        for (long price : List.of(1L, 7L)) {
            assertEquals(onTheRow.answering(List.of(price(price))),
                    inATable.answering(List.of(price(price))),
                    () -> "what the two answer for " + price);
        }
    }

    /** The one stand-in of the one row of a module's only behavior that depends on something. */
    private static StandsIn onlyStandIn(String module) {
        CheckedRow row = behavior(CheckedProgram.of(List.of(module)), "rateOf").rows().get(0);
        return assertInstanceOf(CheckedRow.WithStandIns.class, row.statement())
                .standsIn().get(0);
    }

    /** A price as an output would hand it over, which is what a newtype is written as. */
    private static souther.compiler.observe.ObservedValue price(long value) {
        java.util.Map<String, souther.compiler.observe.ObservedValue> fields =
                souther.compiler.observe.ObservedValue.fields();
        fields.put("value", new souther.compiler.observe.ObservedValue.Integer(value));
        return new souther.compiler.observe.ObservedValue.Constructed(
                souther.compiler.types.TypeSymbols.declared(
                        new souther.compiler.types.TypeKey("demo", "Price")), fields);
    }

    /** The rows of every behavior that depends on something, in the order they are written. */
    private static List<CheckedRow> rowsOf(CheckedProgram program) {
        List<CheckedRow> rows = new ArrayList<>();
        for (CheckedModule module : program.modules()) {
            for (CheckedBehavior behavior : module.behaviors()) {
                rows.addAll(behavior.rows());
            }
        }
        return rows;
    }

    private static CheckedBehavior behavior(CheckedProgram program, String name) {
        return program.module("demo").behavior(new ValueName.Behavior("demo", name));
    }
}
