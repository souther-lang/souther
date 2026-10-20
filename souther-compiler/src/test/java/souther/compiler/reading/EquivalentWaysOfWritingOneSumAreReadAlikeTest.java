package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static souther.compiler.reading.ReadInteractions.readAll;
import static souther.compiler.reading.ReadInteractions.shape;

/**
 * One total of two choices, written the ways the language lets it be written, is read the same way
 * or is said not to be, and is never read as if it decided nothing.
 *
 * <p>The ways are the places a choice can be made and a list can come from: the operands of an
 * operator, the elements of a list written in the body, a list a name holds, a closure that is a
 * name, a closure that hands its argument on, a choice made when the element is written and one
 * made when its worth is. A reading that knows only some of them answers for the rest by finding
 * nothing, and finding nothing reads as a behavior whose decisions meet nowhere. So this holds the
 * whole table to one question: for every way of writing a total that is a function of two
 * decisions, is there a meeting, or is there a reason there is not.
 */
class EquivalentWaysOfWritingOneSumAreReadAlikeTest {

    private static final String HEAD = """
            module example.ways

            data Row = { days: Int, pay: Int }

            behavior total : (first: Row, second: Row) -> Int

            """;

    private static final String WORTH = HEAD
            + "let worth (r: Row): Int = if r.days >= 17 then r.pay else 0\n\n";

    private static final String A = "if first.days >= 17 then first.pay else 0";

    private static final String B = "if second.days >= 17 then second.pay else 0";

    /** A body that is an expression, in a model with no helper. */
    private static String body(String expression) {
        return HEAD + "let total (first, second) =\n    " + expression + "\n";
    }

    /** What each way of writing the total reads as: one meeting of two decisions, or none. */
    private static final Map<String, String> SOURCES = new LinkedHashMap<>();

    static {
        SOURCES.put("two ifs added", body("(" + A + ") + (" + B + ")"));
        SOURCES.put("a list of two ifs", body("List.sum([ " + A + ", " + B + " ])"));
        SOURCES.put("a list a name holds",
                body("{ let xs = [ " + A + ", " + B + " ]\n    List.sum(xs) }"));
        SOURCES.put("each choice named",
                body("{ let a = " + A + "\n    let b = " + B + "\n    List.sum([ a, b ]) }"));
        SOURCES.put("each choice named, added",
                body("{ let a = " + A + "\n    let b = " + B + "\n    a + b }"));
        SOURCES.put("a closure that hands its argument on",
                body("List.sum(List.map(x -> x, [ " + A + ", " + B + " ]))"));
        SOURCES.put("a closure that chooses",
                body("List.sum(List.map(r -> if r.days >= 17 then r.pay else 0,"
                        + " [ first, second ]))"));
        SOURCES.put("a closure that chooses under its own let",
                body("List.sum(List.map(r -> { let s = if r.days >= 17 then r.pay else 0\n"
                        + "    s }, [ first, second ]))"));
        SOURCES.put("a filter",
                body("List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17,"
                        + " [ first, second ])))"));
        SOURCES.put("a count of what a filter keeps",
                body("List.length(List.filter(r -> r.days >= 17, [ first, second ]))"));
        SOURCES.put("a helper that chooses, added",
                WORTH + "let total (first, second) = worth(first) + worth(second)\n");
        SOURCES.put("a helper that chooses, in a list",
                WORTH + "let total (first, second) = List.sum([ worth(first), worth(second) ])\n");
        SOURCES.put("a helper that chooses, as the closure",
                WORTH + "let total (first, second) = List.sum(List.map(worth, [ first, second ]))\n");
        SOURCES.put("a helper that filters", HEAD
                + "let kept (a: Row, b: Row): List<Row> = List.filter(r -> r.days >= 17, [ a, b ])\n\n"
                + "let total (first, second) = List.sum(List.map(r -> r.pay, kept(first, second)))\n");
        SOURCES.put("a helper that totals", HEAD
                + "let pays (a: Row, b: Row): Int =\n"
                + "    List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17, [ a, b ])))\n\n"
                + "let total (first, second) = pays(first, second)\n");
    }

    /** Ways whose decisions are made among elements another closure made, which no application
     *  number of this one is. They are said not to be joined. */
    private static final Map<String, String> NOT_JOINED = new LinkedHashMap<>();

    static {
        NOT_JOINED.put("a choice made, then written out again",
                body("List.sum(List.flatMap(r -> [ r, r ], List.map(r -> if r.days >= 17"
                        + " then r.pay else 0, [ first, second ])))"));
    }

    @Test
    void everyWayOfWritingTheTotalIsOneMeetingOfTwoDecisions() {
        SOURCES.forEach((way, source) ->
                assertEquals(List.of(List.of(2, 2)), shape(readAll(source, "total").interactions()),
                        way));
        SOURCES.forEach((way, source) ->
                assertEquals(List.of(), readAll(source, "total").notJoined(), way));
    }

    @Test
    void aTotalThatDecidesNothingIsReadAsNone() {
        CoverageRead.Read read = readAll(body("List.sum(List.map(r -> r.pay,"
                + " [ first, second ]))"), "total");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(), read.notJoined());
    }

    /** Whatever the way, a total that is a function of decisions is a meeting or is said not to be
     *  one. The table above is every way it is known to be written; a way added to it that finds
     *  neither is the defect this holds against. */
    @Test
    void noWayIsReadAsIfItDecidedNothing() {
        List<String> silent = new ArrayList<>();
        Map<String, String> every = new LinkedHashMap<>(SOURCES);
        every.putAll(NOT_JOINED);
        every.forEach((way, source) -> {
            CoverageRead.Read read = readAll(source, "total");
            if (read.interactions().isEmpty() && read.notJoined().isEmpty()) {
                silent.add(way);
            }
        });
        assertEquals(List.of(), silent, "ways read as if they decided nothing");
        assertFalse(every.isEmpty());
    }

    @Test
    void whereTheChoiceWasMadeAmongElementsAnotherClosureMadeItIsSaidNotJoined() {
        NOT_JOINED.forEach((way, source) -> {
            CoverageRead.Read read = readAll(source, "total");
            assertEquals(List.of(), read.interactions(), way);
            assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_NUMBERED), read.notJoined(), way);
        });
    }

    private static final String ACTIVE = """
            module example.ways

            data Row = { days: Int, pay: Int, active: Bool }

            behavior total : (first: Row, second: Row) -> Int

            let total (first, second) =
                %s
            """;

    private static CoverageRead.Read readActive(String expression) {
        return readAll(ACTIVE.formatted(expression), "total");
    }

    /**
     * A count and a total of the same elements are made of the same decisions. What keeps an
     * element and is not one comparison is said not to be joined for both, however the two are
     * written.
     */
    @Test
    void aCountIsNoMoreSilentThanATotalOfTheSameKeptElements() {
        String kept = "List.filter(r -> r.active, [ first, second ])";

        assertEquals(List.of(WhyNotJoined.NOT_ONE_COMPARISON),
                readActive("List.length(" + kept + ")").notJoined());
        assertEquals(List.of(WhyNotJoined.NOT_ONE_COMPARISON),
                readActive("List.sum(List.map(r -> 1, " + kept + "))").notJoined());
    }

    /**
     * Only a count that a comparison is made of, kept by a quantifier, is the statements' to read.
     * The same count handed back as the answer is no comparison of statements, and the decisions
     * that keep its elements are still met.
     */
    @Test
    void aQuantifierKeepingIsLeftToTheStatementsOnlyWhereTheCountIsCompared() {
        String kept = "List.length(List.filter(r -> List.all(x -> x.days >= r.days,"
                + " [ first, second ]), [ first, second ]))";

        assertEquals(List.of(),
                readActive("if " + kept + " == 1 then 1 else 2").notJoined());
        assertEquals(List.of(WhyNotJoined.NOT_ONE_COMPARISON), readActive(kept).notJoined());
        assertEquals(List.of(WhyNotJoined.NOT_ONE_COMPARISON),
                readActive("{ let n = " + kept + "\n    if n == 1 then 1 else 2 }").notJoined());
    }

    private static final String FLAGGED = """
            module example.ways

            data Row = { days: Int, pay: Int, active: Bool }

            behavior total : (first: Row, second: Row, flag: Bool) -> Int

            let total (first, second, flag) =
                %s
            """;

    private static CoverageRead.Read readFlagged(String expression) {
        return readAll(FLAGGED.formatted(expression), "total");
    }

    /**
     * A condition that is the same on every run is no decision, kept or not: a filter that keeps
     * everything is the list written without it, and one that keeps nothing leaves no element to
     * decide anything. Neither is a meeting that went unmeasured.
     */
    @Test
    void aConditionThatIsSettledDecidesNothing() {
        for (String settled : List.of("true", "false")) {
            String kept = "List.filter(r -> " + settled + ", [ first, second ])";

            assertEquals(List.of(), readFlagged("List.sum(List.map(r -> r.pay, " + kept + "))")
                    .notJoined(), settled);
            assertEquals(List.of(), readFlagged("List.length(" + kept + ")").notJoined(), settled);
        }
    }

    /**
     * Whether there are two decisions is settled before anything is read of them, so a decision
     * that cannot be read is no more a meeting than one that can: one comparison whose number no
     * input holds is one decision.
     */
    @Test
    void oneDecisionThatCannotBeReadIsStillOnlyOne() {
        CoverageRead.Read read = readFlagged(
                "List.sum(List.map(r -> if r.days * r.days > 10 then 5 else 0, [ first ]))");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(), read.notJoined());
    }

    /**
     * A choice made once and named is one decision however often its name is used, and a choice
     * made again on each application of a closure is as many as there are applications. What the
     * reading cannot place it counts as its own, so it never counts fewer than there are.
     */
    @Test
    void aChoiceIsCountedAsOftenAsItIsMade() {
        assertEquals(List.of(), readFlagged("{ let chosen = if flag then 1 else 0\n"
                + "    List.sum(List.map(x -> x, [ chosen, chosen ])) }").notJoined());
        assertEquals(List.of(), readFlagged("{ let chosen = if flag then 1 else 0\n"
                + "    List.sum(List.map(x -> x + 0, [ chosen, chosen ])) }").notJoined());

        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), readFlagged(
                "List.sum(List.flatMap(a -> { let c = if a.active then 1 else 0\n"
                        + "    List.map(x -> x, [ c ]) }, [ first, second ]))").notJoined());
        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), readFlagged(
                "List.sum(List.flatMap(a -> [ if a.active then 1 else 0 ], [ first, second ]))")
                .notJoined());
        assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), readFlagged(
                "{ let a = if flag then 1 else 0\n    let b = if second.active then 1 else 0\n"
                        + "    List.sum(List.map(x -> x + 0, [ a, b ])) }").notJoined());
    }

    /** A decision that nothing else is decided beside meets nothing, read or not. */
    @Test
    void oneDecisionAloneIsNoMeetingToLeaveUnjoined() {
        CoverageRead.Read read = readActive(
                "List.sum(List.map(r -> r.pay, List.filter(r -> r.active, [ first ])))");

        assertEquals(List.of(), read.interactions());
        assertEquals(List.of(), read.notJoined());
    }

    /** The same element written out twice is one decision made twice, not two. */
    @Test
    void anElementWrittenOutTwiceIsStillOneDecision() {
        CoverageRead.Read read = readActive("List.sum(List.map(r -> r.pay, List.flatMap("
                + "r -> [ r, r ], List.filter(r -> r.active, [ first ]))))");

        assertEquals(List.of(), read.notJoined());
    }

    /**
     * Branches that come to the same value are still a choice. A meeting is of the decisions that
     * settle a value, and a path through a body is one whatever the value at its end: the operands
     * of an operator, the elements of a list and the closure that chooses all count them alike.
     */
    @Test
    void branchesThatComeToTheSameValueAreCountedAlikeWhereverTheyAreWritten() {
        String same = "if %s.days >= 17 then 5 else 5";
        String plus = "(" + same.formatted("first") + ") + (" + same.formatted("second") + ")";
        String list = "List.sum([ " + same.formatted("first") + ", " + same.formatted("second") + " ])";
        String map = "List.sum(List.map(r -> if r.days >= 17 then 5 else 5, [ first, second ]))";

        for (String expression : List.of(plus, list, map)) {
            assertEquals(List.of(List.of(2, 2)),
                    shape(readAll(body(expression), "total").interactions()), expression);
        }
    }

    /**
     * An element worth what an empty total is worth does not change a total, kept or not, and what
     * keeps it is no decision of the total's. The others still are.
     */
    @Test
    void anElementWorthNothingIsNoDecisionOfTheTotal() {
        String source = """
                module example.ways

                behavior total : (first: Int, second: Int) -> Int

                let total (first, second) = List.sum(List.filter(x -> x > 0, [ 0, first, second ]))
                """;
        CoverageRead.Read read = readAll(source, "total");

        assertEquals(List.of(List.of(2, 2)), shape(read.interactions()),
                "the two elements that can be worth something");
        assertEquals(List.of(), read.notJoined());
    }
}
