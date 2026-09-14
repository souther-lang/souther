package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.partition.ReadingGap;
import souther.compiler.publish.WeakeningWord;
import souther.compiler.query.Weakening;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every reason a reading of a border came to no number reaches the report as a sentence of its own.
 *
 * <p>The reading tells a value an observation stopped from a position the walk never reached and
 * from a row that never came, and carries which it was through the quantity, the point and the
 * weakening. What it is carried <em>for</em> is that a reader is told which one happened; a
 * projection answering one sentence for two takes the difference out at the last step, and
 * everything upstream of it becomes a distinction nobody can see.
 *
 * <p><b>The sentence, and not the word.</b> {@link WeakeningWord} groups the reasons more coarsely
 * than the reading tells them apart, which is a decision rather than a loss: the reason itself
 * travels underneath and is what the sentence is written from. So the census is over sentences, and
 * what is asked of the words is that they group the reasons the way this was decided to group them
 * — written out below, so that a fold added later is one somebody had to write down.
 *
 * <p><b>Over the cases and not over a list somebody wrote.</b> The reasons are asked of the sealed
 * type, and the codes an observation can arrive with are asked of the values that carry one, so a
 * reason or a code added anywhere arrives here as a case with no sentence rather than as one it
 * quietly shares.
 */
class EveryReasonAReadingMetIsSaidInItsOwnSentenceTest {

    /**
     * As many sentences as there are reasons, and no two reasons under one sentence.
     *
     * <p>Both halves. Equal counts alone pass for a writer that says one sentence twice and another
     * never, and distinctness alone passes for one that leaves a reason out.
     */
    @Test
    void eachReasonHasASentenceAndNoTwoShareOne() {
        List<ReadingGap> reasons = everyReason();
        Set<String> said = new LinkedHashSet<>();
        for (ReadingGap each : reasons) {
            said.add(AdequacyReport.atTheBorder(each));
        }

        assertEquals(reasons.size(), said.size(),
                () -> "two reasons a reading met came out as one sentence: " + reasons + " to "
                        + said);
    }

    /**
     * And each word stands over the reasons this decided to put under it.
     *
     * <p>The decision itself, since nothing else keeps it. A place the walk could not reach and a
     * row that never came are one word because a reader weighing the document does the same thing
     * about both; they are apart from a position that was read and holds nothing, which is news
     * about the model rather than about this compiler's reach. What travels underneath is the
     * reason, so the grouping costs a reader nothing — and it is written here because a grouping
     * nothing states is one the next fold can join without saying so.
     *
     * <p><b>Not that reasons under one word are weakened alike.</b> They are not: the codes an
     * observation arrives with come out as one word and answer differently about whether a wider
     * run would have got a number. That is exactly why the reason and not the word is what the
     * sentence is written from, and a test asserting the tidier property would be asserting
     * something the vocabulary has never kept.
     */
    @Test
    void eachWordStandsOverTheReasonsThisDecidedToPutUnderIt() {
        Map<WeakeningWord, Set<String>> under = new LinkedHashMap<>();
        for (ReadingGap each : everyReason()) {
            under.computeIfAbsent(wordFor(each), _ -> new LinkedHashSet<>())
                    .add(each.getClass().getSimpleName());
        }

        // The word each group is under, and not only which reasons share one. A word is written
        // into the document and named in the schema, so which reasons it stands over is as much of
        // the contract as which of them are together — grouped alone, the words could be dealt out
        // among the groups differently and every reader of a published document would be told
        // something else about the same reasons.
        assertEquals(Map.of(
                        WeakeningWord.BORDER_VALUE_UNREADABLE, Set.of("Observation"),
                        WeakeningWord.BORDER_VALUE_ABSENT, Set.of("NoValue"),
                        WeakeningWord.BORDER_OBSERVATION_UNAVAILABLE,
                                Set.of("CouldNotWalk", "CouldNotReadRow")),
                under,
                () -> "the words no longer stand over the reasons they were meant to: " + under);
    }

    private static WeakeningWord wordFor(ReadingGap why) {
        return AdequacyReport.wordFor(new Weakening.BorderValueUnreadable(null, why));
    }

    /**
     * One of each, taken from what the type permits rather than from what a reader remembers.
     *
     * <p>An observation carries a code, and which codes one can carry is asked of the values that
     * carry them rather than named here — a value says whether it went unread and with which word,
     * so the codes an observation of a value arrives with are however many those turn out to be.
     * Picked by hand, the population would be as wide as whoever wrote it remembered, and a word
     * that groups two of them would look like a word that groups one.
     */
    private static List<ReadingGap> everyReason() {
        List<ReadingGap> out = new ArrayList<>();
        for (Class<?> permitted : ReadingGap.class.getPermittedSubclasses()) {
            switch (permitted.getSimpleName()) {
                case "Observation" -> everyCodeAValueArrivesUnreadWith().forEach(
                        code -> out.add(ReadingGap.of(code)));
                case "NoValue" -> out.add(ReadingGap.NO_VALUE);
                case "CouldNotWalk" -> out.add(ReadingGap.COULD_NOT_WALK);
                case "CouldNotReadRow" -> out.add(ReadingGap.COULD_NOT_READ_ROW);
                // A reason added to the type and not to this list. Written as a failure rather than
                // skipped: a reason nothing here can build is one nothing here is checking.
                default -> throw new IllegalStateException(
                        "a reason a reading can meet that this test cannot make: " + permitted);
            }
        }
        return out;
    }

    /**
     * The codes a value says it went unread with, asked of every shape a value can take.
     *
     * <p>{@link ObservedValue#unread()} is what every producer of one of these agrees about, and
     * the shapes are asked of the sealed type rather than named here. Named here, the population
     * would be as wide as whoever wrote it remembered — which is how a word that groups two codes
     * came to be checked as a word that groups one.
     */
    private static Set<Incompleteness.Code> everyCodeAValueArrivesUnreadWith() {
        Set<Incompleteness.Code> out = new LinkedHashSet<>();
        for (Class<?> shape : ObservedValue.class.getPermittedSubclasses()) {
            Incompleteness.Code code = oneOf(shape).unread();
            if (code != null) {
                out.add(code);
            }
        }
        return out;
    }

    /**
     * One value of {@code shape}, so that it can be asked whether it went unread.
     *
     * <p>A shape added to {@link ObservedValue} and not to this stops the test rather than being
     * skipped: a shape nothing here can make is a shape whose word nothing here is looking for.
     */
    private static ObservedValue oneOf(Class<?> shape) {
        return switch (shape.getSimpleName()) {
            case "Bool" -> new ObservedValue.Bool(true);
            case "Integer" -> new ObservedValue.Integer(1);
            case "Decimal" -> new ObservedValue.Decimal(java.math.BigDecimal.ONE);
            case "Text" -> new ObservedValue.Text("x");
            case "Temporal" -> new ObservedValue.Temporal("2026-01-01");
            case "Unit" -> new ObservedValue.Unit(null);
            case "Constructed" -> new ObservedValue.Constructed(null, Map.of());
            case "Sequence" -> new ObservedValue.Sequence(List.of());
            case "Mapping" -> new ObservedValue.Mapping(List.of());
            case "Absent" -> new ObservedValue.Absent();
            case "Unknown" -> new ObservedValue.Unknown("nothing read it");
            case "Truncated" -> new ObservedValue.Truncated();
            default -> throw new IllegalStateException(
                    "a shape a value can take that this test cannot make: " + shape);
        };
    }
}
