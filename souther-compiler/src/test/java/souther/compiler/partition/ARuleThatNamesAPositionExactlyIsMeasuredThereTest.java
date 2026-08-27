package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule that names one position is measured at that position, however many times the path it names
 * goes through a declaration.
 *
 * <p><b>Two questions, and only one of them has to be bounded.</b> Enumerating what positions a type
 * can have is unbounded over a declaration that names itself, and the walk stops where a path
 * returns to one it has already opened. Resolving a path a rule wrote is not that question: the path
 * is as long as the author made it, every step of it is taken once, and it ends because the path
 * does. Answered by the same walk, a threshold an author wrote one link down a chain drew no line
 * and the report said the model states nothing there.
 *
 * <p>Which is why this is not "unfold twice". Nothing here chooses a number of unfoldings: five
 * links are measured for the same reason one is, and a model that names none is measured at none.
 */
class ARuleThatNamesAPositionExactlyIsMeasuredThereTest {

    /** A chain, with the threshold one link down. */
    private static final String ONE_LINK = """
            module example.chain

            data Nil
            data Cons = { head: Int, tail: Chain }
            data Chain = Nil | Cons

            behavior f : (c: Chain) -> Int
            let f (c) =
                match c with
                    | Nil -> 0
                    | Cons as k ->
                        match k.tail with
                            | Nil -> 1
                            | Cons as m -> if m.head >= 10 then 2 else 3

            example f | "empty" : (Nil) -> 0
            """;

    /** The same, with the threshold five links down. */
    private static final String FIVE_LINKS = """
            module example.chain

            data Nil
            data Cons = { head: Int, tail: Chain }
            data Chain = Nil | Cons

            behavior f : (c: Chain) -> Int
            let f (c) =
                match c with
                    | Nil -> 0
                    | Cons as a -> match a.tail with
                        | Nil -> 1
                        | Cons as b -> match b.tail with
                            | Nil -> 2
                            | Cons as d -> match d.tail with
                                | Nil -> 3
                                | Cons as e -> match e.tail with
                                    | Nil -> 4
                                    | Cons as g -> if g.head >= 10 then 5 else 6

            example f | "empty" : (Nil) -> 0
            """;

    /** One link down, the line is drawn and both sides of it are asked for. */
    @Test
    void aThresholdOneLinkDownIsMeasured() {
        String report = report(ONE_LINK);

        assertTrue(report.contains("no row is at the ON point f/c@Cons.tail@Cons.head = 10"),
                report);
        assertTrue(report.contains("no row is at the OFF point f/c@Cons.tail@Cons.head = 9"),
                report);
    }

    /**
     * And five links down it is drawn at the fifth, not at whichever link a limit would have
     * stopped at.
     *
     * <p>The whole path, spelled out. A reading that unfolded a fixed number of times would draw
     * this line somewhere shorter or not at all, and both are reports about a rule the author did
     * not write.
     */
    @Test
    void aThresholdFiveLinksDownIsMeasuredAtTheFifth() {
        String report = report(FIVE_LINKS);

        assertTrue(report.contains("no row is at the ON point "
                        + "f/c@Cons.tail@Cons.tail@Cons.tail@Cons.tail@Cons.head = 10"),
                report);
    }

    /**
     * And naming one position does not enumerate the rest.
     *
     * <p>The control. What makes this safe is that a rule resolves one path rather than asking what
     * a recursive type can hold, so the positions the report divides stay the ones the walk found:
     * the classes are at the first link and nowhere below it.
     */
    @Test
    void namingOneLinkDoesNotEnumerateTheOthers() {
        String report = report(FIVE_LINKS);

        assertTrue(report.contains("no row is in `Nil` at c@Cons.tail"), report);
        // The second link, which no rule names. Matched to the end of the line so that the position
        // the threshold does name — five links down and spelled through this one — is not read as
        // this one having been enumerated.
        assertFalse(report.lines().anyMatch(each -> each.endsWith("at c@Cons.tail@Cons.tail")),
                () -> "the walk stopped at the first return, and only the named line goes past it:\n"
                        + report);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
