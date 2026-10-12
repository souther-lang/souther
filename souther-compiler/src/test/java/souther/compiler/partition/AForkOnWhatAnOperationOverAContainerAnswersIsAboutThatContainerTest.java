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
 * An {@code if} on what an operation over a container answers turns on that container, and on no
 * other position.
 *
 * <p>The tree a run is read in has the operation expanded, so the fork stands on a value no
 * position is and the reading of the runs names no subject for it. Read as a decision whose subject
 * nobody could name, it left what the body tells apart unknown at every position — {@code more}
 * here, which nothing in the body reads. The tree the operations stand in reads the condition as a
 * statement about {@code regions}, and that is all it is about.
 */
class AForkOnWhatAnOperationOverAContainerAnswersIsAboutThatContainerTest {

    private static final String MODEL = """
            module gate
            data North
            data South
            data Region = North | South
            data Rs = { regions: List<Region>, more: List<Region> }
            data Out = { n: Int }

            behavior ok : (rs: Rs) -> Bool

            behavior every : (rs: Rs) -> Out
                constructs Out
            let every (rs) = Out { n = if List.all(r -> r == North, rs.regions) then 1 else 0 }

            behavior asked : (rs: Rs) -> Out
                depends on ok
                constructs Out
            let asked (rs, ok) = Out { n = if ok(rs) then 1 else 0 }
            """;

    @Test
    void aPositionTheStatementDoesNotReadIsUntouched() {
        Map<String, BodyDistinction> told = toldApart("every");

        assertInstanceOf(BodyDistinction.Untouched.class, told.get("rs.more[*]"),
                () -> "nothing `List.all` states reads `more`: " + told);
        assertInstanceOf(BodyDistinction.Unread.class, told.get("rs.regions[*]"),
                () -> "and what it states of `regions` is not put to its classes: " + told);
        assertEquals(true, ((BodyDistinction.Unread) told.get("rs.regions[*]")).unplacedHere(),
                () -> "it is about `regions` itself: " + told);
    }

    @Test
    void aForkOnWhatADependencyAnswersStillMayBeAboutAnyPosition() {
        Map<String, BodyDistinction> told = toldApart("asked");

        assertEquals(new BodyDistinction.Unread(List.of(List.of("North", "South")), false),
                told.get("rs.more[*]"),
                () -> "what `ok` answers may turn on anything it was handed: " + told);
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
        return compilation.db().ask(new Adequacy.Coverage("gate")).value();
    }
}
