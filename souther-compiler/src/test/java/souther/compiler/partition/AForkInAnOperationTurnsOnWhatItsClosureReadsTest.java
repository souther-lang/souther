package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A fork in the body of an operation the language defines, on what the closure the model handed it
 * answers, turns on what that closure reads of the input and on nothing else.
 *
 * <p>{@code List.filter} is a fold whose step asks the closure of each element, so the tree a run is
 * read in holds a fork of the library's on the closure's body, with the element bound to a name no
 * position is. Read as a decision whose subject nobody could name, it left what the body tells apart
 * unknown at every position. The tree the operations stand in reads the closure's answer on each
 * element, and what that statement reads is what the fork may turn on.
 *
 * <p>Nothing here says which classes go which way through such a fork: a position it may turn on is
 * read in part, and one it cannot turn on is left to the ways that read it.
 */
class AForkInAnOperationTurnsOnWhatItsClosureReadsTest {

    private static final String MODEL = """
            module kept
            data North
            data South
            data Region = North | South
            data Meeting = { r: Region, s: Region }
            data Rs = { ms: List<Meeting>, other: Region, regions: List<Region>,
                        more: List<Region> }
            data Out = { n: Int }

            behavior ok : (rs: Rs) -> Bool

            behavior byAConstant : (rs: Rs) -> Out
                constructs Out
            let byAConstant (rs) = Out { n = List.length(List.filter(m -> m.r == North, rs.ms)) }

            behavior byAnotherPosition : (rs: Rs) -> Out
                constructs Out
            let byAnotherPosition (rs) =
                Out { n = List.length(List.filter(m -> m.r == rs.other, rs.ms)) }

            behavior everything : (rs: Rs) -> Out
                constructs Out
            let everything (rs) = Out { n = List.length(List.filter(m -> true, rs.ms)) }

            let pick (xs: List<Meeting>, k: Region): List<Meeting> =
                List.filter(m -> m.r == k, xs)

            behavior twice : (rs: Rs) -> Out
                constructs Out
            let twice (rs) =
                Out { n = List.length(pick(rs.ms, North)) + List.length(pick(rs.ms, rs.other)) }

            behavior nested : (rs: Rs) -> Out
                constructs Out
            let nested (rs) = Out { n = List.length(List.filter(
                m -> List.all(r -> r == North, rs.regions), rs.ms)) }

            behavior branching : (rs: Rs) -> Out
                constructs Out
            let branching (rs) = {
                let unused = List.all(m -> if m.r == North then m.s == North else true, rs.ms)
                Out { n = 0 }
            }

            behavior asked : (rs: Rs) -> Out
                depends on ok
                constructs Out
            let asked (rs, ok) = Out { n = List.length(List.filter(m -> ok(rs), rs.ms)) }
            """;

    @Test
    void aPositionTheClosureDoesNotReadIsUntouched() {
        Map<String, BodyDistinction> told = toldApart("byAConstant");

        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.more[*]"),
                () -> "the closure reads each meeting's `n` and nothing of `more`: " + told);
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.other"), () -> "" + told);
        assertEquals(true, unreadHere(told.get("rs.ms[*].r")),
                () -> "and what it reads is read in part: " + told);
    }

    @Test
    void aPositionTheClosureReadsBesideTheElementIsReadInPart() {
        Map<String, BodyDistinction> told = toldApart("byAnotherPosition");

        assertEquals(true, unreadHere(told.get("rs.other")),
                () -> "the line each element is held to is `other`: " + told);
        assertEquals(true, unreadHere(told.get("rs.ms[*].r")), () -> "" + told);
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.more[*]"), () -> "" + told);
    }

    @Test
    void aClosureAnsweringTheSameForEveryElementReadsNoneOfThem() {
        Map<String, BodyDistinction> told = toldApart("everything");

        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.ms[*].r"),
                () -> "keeping every meeting reads nothing of one: " + told);
    }

    @Test
    void eachCallOfAHelperIsReadWithWhatThatCallHandedIt() {
        Map<String, BodyDistinction> told = toldApart("twice");

        assertEquals(true, unreadHere(told.get("rs.other")),
                () -> "the second call holds each meeting to `other`: " + told);
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.more[*]"), () -> "" + told);
    }

    @Test
    void aClosureThatAsksAnotherOperationTurnsOnWhatThatOneReads() {
        Map<String, BodyDistinction> told = toldApart("nested");

        assertEquals(true, unreadHere(told.get("rs.regions[*]")),
                () -> "whether a meeting is kept is whether every region is `North`: " + told);
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.more[*]"), () -> "" + told);
        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.ms[*].r"), () -> "" + told);
    }

    /**
     * A closure whose body is an {@code if} answers with what the {@code if} answers, which reads
     * what both its arms read; the {@code if} itself turns on its condition alone.
     */
    @Test
    void aForkThatIsAClosuresBodyTurnsOnItsConditionAndNotOnItsArms() {
        Map<String, BodyDistinction> told = toldApart("branching");

        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.ms[*].s"),
                () -> "`s` is what the `then` arm answers, and nothing forks on it: " + told);
    }

    @Test
    void aClosureOnWhatADependencyAnswersMayTurnOnAnything() {
        Map<String, BodyDistinction> told = toldApart("asked");

        assertEquals(new BodyDistinction.Unread(List.of(List.of("North", "South")), false),
                told.get("rs.more[*]"),
                () -> "what `ok` answers may turn on anything it was handed: " + told);
    }

    /** Whether {@code told} says the body says something about the position it did not read. */
    private static boolean unreadHere(BodyDistinction told) {
        return told instanceof BodyDistinction.Unread unread && unread.unplacedHere();
    }

    /** What each behavior of the model tells apart, read once for every test here. */
    private static final Map<String, PartitionEvidence> MEASURED = measured();

    private static Map<String, BodyDistinction> toldApart(String behavior) {
        Map<String, BodyDistinction> out = new LinkedHashMap<>();
        MEASURED.get(behavior).axes().forEach(axis -> out.put(axis.name(), axis.toldApart()));
        return out;
    }

    private static Map<String, PartitionEvidence> measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code()).toList(),
                "the model under test compiles");
        return compilation.db().ask(new Adequacy.Coverage("kept")).value();
    }
}
