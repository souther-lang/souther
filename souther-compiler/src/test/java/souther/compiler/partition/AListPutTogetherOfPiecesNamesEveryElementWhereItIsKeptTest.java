package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.meaning.Proposition;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a name an operation handed an element of a list on stands for, where the list was put
 * together of a piece of each element of a list written out: every element, in the order a walk of
 * the list meets them and as often as each is there, each with the truths it was kept by.
 *
 * <p>Read off the body the analysis reads, which is where the operations that put a list together
 * still stand as themselves. Each truth is read where it was decided, which is how a reader placing
 * an application of a closure reads it: one that holds whatever the row is, one that holds on no
 * row, or one about the input.
 */
class AListPutTogetherOfPiecesNamesEveryElementWhereItIsKeptTest {

    /** A flatMap holds every element of every piece, the pieces in the order of what it walked. */
    @Test
    void aFlatMapNamesEveryElementOfEveryPieceInOrder() {
        assertEquals("[1, 1, 2, 2]", standingOn(
                "List.flatMap(t -> [ Big { threshold = t }, Big { threshold = t } ], [ 1, 2 ])"));
    }

    /** And so where each piece is what a map answered. */
    @Test
    void aFlatMapOfMapsNamesEveryElementOfEveryMap() {
        assertEquals("[1, 3, 2, 3]", standingOn(
                "List.flatMap(t -> List.map(u -> Big { threshold = u }, [ t, 3 ]), [ 1, 2 ])"));
    }

    /**
     * A filter names every element it was handed, each kept where its closure holds of it — the one
     * it drops as well, kept on no row, and not left out by this reading.
     */
    @Test
    void aFilterNamesEveryElementItWasHandedEachWhereItIsKept() {
        assertEquals("[1 where [no row], 2 where [every row]]", standingOn(
                "List.filter(k -> k.threshold > 1, [ Big { threshold = 1 }, Big { threshold = 2 } ])"));
    }

    /**
     * What is there on some row, as a reader is handed it: an element a filter drops on every row
     * is left out, and one it keeps on every row is kept by nothing.
     */
    @Test
    void whatIsThereOnSomeRowLeavesOutWhatAFilterDropsOnEveryRow() {
        assertEquals("[2]", there(
                "List.filter(k -> k.threshold > 1, [ Big { threshold = 1 }, Big { threshold = 2 } ])"));
    }

    /** And keeps what a filter keeps by what the row holds, still kept by it. */
    @Test
    void whatIsThereOnSomeRowKeepsWhatTheRowDecides() {
        assertEquals("[1 where [the row], 2 where [the row]]", there(
                "List.filter(k -> k.threshold > n, [ Big { threshold = 1 }, Big { threshold = 2 } ])"));
    }

    /** A filter keeping by what the row holds keeps each element where the row says so. */
    @Test
    void aFilterKeepingByTheInputKeepsEachWhereTheRowDoes() {
        assertEquals("[1 where [the row], 2 where [the row]]", standingOn(
                "List.filter(k -> k.threshold > n, [ Big { threshold = 1 }, Big { threshold = 2 } ])"));
    }

    /**
     * What an element was kept by goes with every piece made of it, decided first: the truths the
     * outer filter kept it by stand before the inner one's.
     */
    @Test
    void whatAnElementWasKeptByGoesWithThePiecesMadeOfIt() {
        assertEquals("[1 where [no row, no row], 2 where [every row, no row],"
                        + " 3 where [every row, every row]]",
                standingOn("List.flatMap(t -> List.filter(b -> b.threshold > 2,"
                        + " [ Big { threshold = t } ]), List.filter(t -> t > 1, [ 1, 2, 3 ]))"));
    }

    /**
     * A filter keeping the lists whose elements all differ by a key keeps each where the keys
     * written into it all differ: how many different keys a list written out comes to is the same
     * on every row.
     */
    @Test
    void aFilterByKeysAllDifferingKeepsEachListWhereTheKeysWrittenDiffer() {
        assertEquals("[1 where [every row], 2 where [every row], 3 where [no row],"
                        + " 3 where [no row]]",
                standingOn("List.flatMap(s -> s, List.filter(s -> List.allDistinctBy("
                        + "b -> b.threshold, s), [ [ Big { threshold = 1 }, Big { threshold = 2 } ],"
                        + " [ Big { threshold = 3 }, Big { threshold = 3 } ] ]))"));
    }

    /** An {@code if} holds every element of each arm, each kept where its arm is taken. */
    @Test
    void anIfNamesTheElementsOfEachArmWhereTheArmIsTaken() {
        assertEquals("[1 where [the row], 2 where [the row]]", standingOn(
                "if n > 1 then [ Big { threshold = 1 } ] else [ Big { threshold = 2 } ]"));
    }

    /** An arm no run takes holds nothing there, and one every run takes is kept by nothing. */
    @Test
    void anArmNoRunTakesHoldsNothingThere() {
        assertEquals("[1]", there(
                "if 1 > 0 then [ Big { threshold = 1 } ] else [ Big { threshold = 2 } ]"));
    }

    /** A {@code match} holds every element of each arm, kept where the arm is taken. */
    @Test
    void aMatchNamesTheElementsOfEachArmWhereTheArmIsTaken() {
        assertEquals("[1 where [the row], 2 where [the row]]", standingOn(
                "match (if n > 1 then On else Off) with | On -> [ Big { threshold = 1 } ]"
                        + " | Off -> [ Big { threshold = 2 } ]"));
    }

    /** A case no run is leaves its arm holding nothing there. */
    @Test
    void anArmOfAMatchNoRunTakesHoldsNothingThere() {
        assertEquals("[2]", there(
                "match (if 1 > 0 then Off else On) with | On -> [ Big { threshold = 1 } ]"
                        + " | Off -> [ Big { threshold = 2 } ]"));
    }

    /** An attempt holds every element of what it answers where it built the value and where it
     *  departed, each kept where that arm is taken. */
    @Test
    void anAttemptNamesTheElementsOfEachArmWhereTheArmIsTaken() {
        assertEquals("[1 where [the row], 2 where [the row]]", standingOn(
                "if Level(n) as l then [ Big { threshold = 1 } ] else [ Big { threshold = 2 } ]"));
    }

    /** What the arm is taken on goes before what a filter in it kept an element by. */
    @Test
    void whatAnArmIsTakenOnGoesBeforeWhatIsKeptInIt() {
        assertEquals("[1 where [the row, no row], 2 where [the row, every row]]", standingOn(
                "if n > 1 then List.filter(k -> k.threshold > 1, [ Big { threshold = 1 },"
                        + " Big { threshold = 2 } ]) else []"));
    }

    /** A choice a flatMap's step makes is read on each element it is handed. */
    @Test
    void aChoiceInAFlatMapIsReadOnEachElement() {
        assertEquals("[2]", there(
                "List.flatMap(t -> if t > 1 then [ Big { threshold = t } ] else [], [ 1, 2 ])"));
    }

    /** An arm this cannot write out leaves the whole unwritten, and not the other arms. */
    @Test
    void anArmThatCannotBeWrittenOutLeavesTheWholeAnElement() {
        assertEquals("Element", standingOn("if n > 1 then [ Big { threshold = 1 } ] else"
                + " List.append([ Big { threshold = 1 } ], [ Big { threshold = 2 } ])"));
    }

    /** A piece this reading cannot write out leaves the whole unwritten, and not a part of it. */
    @Test
    void aPieceThatCannotBeWrittenOutLeavesTheWholeAnElement() {
        assertEquals("Element", standingOn("List.flatMap(t -> List.append([ Big { threshold = t } ],"
                + " [ Big { threshold = t } ]), [ 1, 2 ])"));
    }

    /** A list that could be written out and holds more than is said so, and is no element. */
    @Test
    void aListPastWhatIsWrittenOutIsSaidToBe() {
        String ts = "[ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11 ]";
        assertEquals("MoreThanAreWrittenOut", standingOn(("List.flatMap(a -> List.flatMap(b ->"
                + " List.map(c -> Big { threshold = c }, %s), %s), %s)").formatted(ts, ts, ts)));
    }

    /**
     * The walk writes out at least as many as a condition is read on. Below it, a list every reader
     * would read would be said to hold more than is written out.
     */
    @Test
    void theWalkWritesOutAsManyAsAConditionIsReadOn() {
        assertTrue(ElementsWrittenOut.MOST_WALKED
                        >= CompositionBudget.READINGS_OF_ONE_CONDITION.maximum(),
                () -> ElementsWrittenOut.MOST_WALKED + " against "
                        + CompositionBudget.READINGS_OF_ONE_CONDITION.maximum());
    }

    /**
     * What the element of {@code ks} the comparison {@code n >= k.threshold} reads stands for: each
     * occurrence's threshold, and how each truth it was kept by reads.
     */
    private static String standingOn(String ks) {
        return occurrencesOf(ks, false);
    }

    /** The same, of the occurrences there on some row, as every reader is handed them
     *  ({@link KeptTruths}). */
    private static String there(String ks) {
        return occurrencesOf(ks, true);
    }

    private static String occurrencesOf(String ks, boolean decided) {
        String source = """
                module g

                data Big = { threshold: Int }
                data On
                data Off
                data Flag = On | Off
                data Level = Int
                    invariant value > 1
                data Yes
                data No

                behavior classify : (n: Int) -> Yes | No
                let classify (n) = {
                        let ks = %s
                        if List.any((k) -> n >= k.threshold, ks) then Yes else No
                    }

                example classify
                    | "none" : (0) -> No
                """.formatted(ks);
        ReadComparisons read = ReadComparisons.ofTheAnalysis(source, "classify");
        ComparisonReadings.Reading over = read.comparisons().stream()
                .filter(each -> each.statement() instanceof ComparisonReadings.Stated.AComparison(
                        var written) && written.left() instanceof Core.Read
                        && written.right() instanceof Core.FieldAccess)
                .findFirst().orElseThrow();
        Core.FieldAccess threshold = (Core.FieldAccess) ((ComparisonReadings.Stated.AComparison)
                over.statement()).comparison().right();
        InputReads at = over.reads();
        ReadMeaning meaning = at.meaningOf((Core.Read) threshold.target(), read.rules().symbols(),
                read.rules().newtypes());
        if (!(meaning instanceof ReadMeaning.OneOf one)) {
            return meaning.getClass().getSimpleName();
        }
        List<String> each = new ArrayList<>();
        // Undecided, every occurrence as written, kept or not: which of them are there is what
        // that shows.
        ReadMeaning.WhereKept deciding = decided
                ? KeptTruths.readIn(read.inputs().reading(read.rules()))
                : ReadMeaning.WhereKept.NOTHING_DECIDED;
        for (ReadMeaning.Occurrence occurrence : one.occurrencesWhere(deciding)) {
            String value = thresholdOf(occurrence.value(), read);
            if (occurrence.keptWhere().isEmpty()) {
                each.add(value);
                continue;
            }
            List<String> kept = new ArrayList<>();
            for (ReadMeaning.Occurrence.Kept by : occurrence.keptWhere()) {
                kept.add(switch (Pullback.ofWhatKeeps(by, read.inputs().reading(read.rules()))
                        .proposition()) {
                    case Proposition.Always(boolean holds) -> holds ? "every row" : "no row";
                    case Proposition.Unread _ -> "unread";
                    default -> "the row";
                });
            }
            each.add(value + " where " + kept);
        }
        return each.toString();
    }

    /** The threshold the value an occurrence stands for was built with, followed to the number. */
    private static String thresholdOf(Denotation value, ReadComparisons read) {
        Core.Construct made = (Core.Construct) Core.withoutStanding(value.at().standing(
                value.value(), read.rules().symbols(), read.rules().newtypes()).value());
        Core written = Core.withoutStanding(value.at().standing(made.values().getFirst().value(),
                read.rules().symbols(), read.rules().newtypes()).value());
        return written instanceof Core.Int number ? Long.toString(number.value())
                : written.getClass().getSimpleName();
    }
}
