package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;

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

            behavior total : (first: Row, second: Row, flag: Bool, threshold: Int) -> Int

            let total (first, second, flag, threshold) =
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

    /** The ways the list a total is over can be handed to it without changing what it holds. */
    private static final Map<String, UnaryOperator<String>> HANDED =
            new LinkedHashMap<>();

    static {
        HANDED.put("as written", list -> list);
        HANDED.put("past a filter that keeps all", list -> "List.filter(r -> true, " + list + ")");
        HANDED.put("past a map that hands on", list -> "List.map(x -> x, " + list + ")");
    }

    /** What a total of two choices is made of, over a list: the choice made by a condition the
     *  reading can name, and by one it cannot. */
    private static final Map<String, UnaryOperator<String>> CHOOSING =
            new LinkedHashMap<>();

    static {
        CHOOSING.put("a closure that chooses", list -> "List.sum(List.map(r -> if r.days >= 17"
                + " then r.pay else 0, " + list + "))");
        CHOOSING.put("a closure that chooses under its own let", list -> "List.sum(List.map(r -> {"
                + " let s = if r.days >= 17 then r.pay else 0\n    s }, " + list + "))");
        CHOOSING.put("a filter", list -> "List.sum(List.map(r -> r.pay, List.filter("
                + "r -> r.days >= 17, " + list + ")))");
    }

    /** Choices made on each application by what the reading cannot name: the total is a function
     *  of as many decisions as there are applications. */
    private static final Map<String, UnaryOperator<String>> UNNAMED =
            new LinkedHashMap<>();

    static {
        UNNAMED.put("a closure that chooses", list -> "List.sum(List.map(r -> if flag then 1"
                + " else 0, " + list + "))");
        UNNAMED.put("a closure that chooses under its own let", list -> "List.sum(List.map(r -> {"
                + " let c = if flag then 1 else 0\n    c }, " + list + "))");
        UNNAMED.put("a closure that writes a choice out", list -> "List.sum(List.flatMap(r -> {"
                + " let c = if flag then 1 else 0\n    [ c ] }, " + list + "))");
        UNNAMED.put("a closure that writes a choice out by a field", list ->
                "List.sum(List.flatMap(r -> [ if r.active then 1 else 0 ], " + list + "))");
    }

    private static final String LIST = "[ first, second ]";

    /**
     * Nothing about how the list reaches the total changes what the total is made of: every way of
     * choosing is the same meeting of two decisions however the list is handed on. The ways are
     * crossed rather than listed, so that a way added to either side is tried with every one of
     * the other.
     */
    @Test
    void howAListIsHandedOnChangesNothingAboutTheMeeting() {
        List<String> differing = new ArrayList<>();
        CHOOSING.forEach((choosing, total) -> HANDED.forEach((handed, hand) -> {
            CoverageRead.Read read = readFlagged(total.apply(hand.apply(LIST)));
            if (!List.of(List.of(2, 2)).equals(shape(read.interactions()))
                    || !read.notJoined().isEmpty()) {
                differing.add(choosing + ", " + handed + ": " + shape(read.interactions())
                        + " " + read.notJoined());
            }
        }));
        assertEquals(List.of(), differing);
    }

    /**
     * A total of choices made on each application is never read as if it decided nothing: it is a
     * meeting or it is said not to be joined, however the list reaches it.
     */
    @Test
    void aChoiceMadeOnEachApplicationIsNeverSilentHoweverTheListIsHandedOn() {
        List<String> silent = new ArrayList<>();
        UNNAMED.forEach((choosing, total) -> HANDED.forEach((handed, hand) -> {
            CoverageRead.Read read = readFlagged(total.apply(hand.apply(LIST)));
            if (read.interactions().isEmpty() && read.notJoined().isEmpty()) {
                silent.add(choosing + ", " + handed);
            }
        }));
        assertEquals(List.of(), silent);
    }

    /**
     * What a filter takes out on every run is no application of the step after it, wherever in the
     * list it stands, and the applications after it are numbered as a run counts them.
     */
    @Test
    void anElementAlwaysTakenOutLeavesTheOtherApplicationsNumbered() {
        List<String> lists = List.of("[ 1, 2 ]", "List.filter(x -> x > 0, [ 0, 1, 2 ])",
                "List.filter(x -> x > 0, [ 1, 0, 2 ])", "List.filter(x -> x > 0, [ 1, 2, 0 ])",
                "List.map(x -> x, List.filter(x -> x > 0, [ 0, 1, 2 ]))");
        List<String> differing = new ArrayList<>();
        for (String list : lists) {
            CoverageRead.Read read = readFlagged("List.sum(List.map(x ->"
                    + " if threshold >= 17 then x else 0, " + list + "))");
            if (!List.of(List.of(2, 2)).equals(shape(read.interactions()))
                    || !read.notJoined().isEmpty()) {
                differing.add(list + ": " + shape(read.interactions()) + " " + read.notJoined());
            }
        }
        assertEquals(List.of(), differing);
    }

    /** The visit each decision of each meeting claims, in the order they are met. */
    private static List<Object> visitsClaimed(List<Interaction> found) {
        return found.stream().<Object>map(group -> group.factors().stream()
                .map(factor -> factor.outcomes().stream()
                        .map(outcome -> outcome.holds().stream()
                                .map(decision -> decision.claims().visit()).toList())
                        .toList())
                .toList()).toList();
    }

    /** Lists of the same two numbers, with what is taken out on every run before, between and
     *  after them, and the ways of handing a list on that change nothing. */
    private static final Map<String, String> TWO_NUMBERS = new LinkedHashMap<>();

    static {
        TWO_NUMBERS.put("as written", "[ 1, 2 ]");
        TWO_NUMBERS.put("one taken out first", "List.filter(x -> x > 0, [ 0, 1, 2 ])");
        TWO_NUMBERS.put("one taken out between", "List.filter(x -> x > 0, [ 1, 0, 2 ])");
        TWO_NUMBERS.put("one taken out last", "List.filter(x -> x > 0, [ 1, 2, 0 ])");
        TWO_NUMBERS.put("two taken out", "List.filter(x -> x > 0, [ 0, 1, 0, 2 ])");
        TWO_NUMBERS.put("past a filter that keeps all", "List.filter(x -> true, [ 1, 2 ])");
        TWO_NUMBERS.put("past a map that hands on", "List.map(x -> x, [ 1, 2 ])");
        TWO_NUMBERS.put("past a flatMap that hands on", "List.flatMap(x -> [ x ], [ 1, 2 ])");
        TWO_NUMBERS.put("taken out, then handed on",
                "List.map(x -> x, List.filter(x -> x > 0, [ 0, 1, 2 ]))");
    }

    /**
     * The visits a meeting claims are the visits a run makes, so they are the same however the
     * elements came to be the list: what a filter before takes out on every run is no visit of
     * the comparison after it. Shape alone does not say so, since a claim on a visit no run makes
     * has the same shape as one on a visit it does.
     */
    @Test
    void theVisitsClaimedAreTheRunsOwnWhateverWasTakenOutBefore() {
        List<String> totals = List.of(
                "List.length(List.filter(x -> threshold > x, %s))",
                "List.sum(List.map(x -> if threshold >= 17 then x else 0, %s))",
                "List.sum(List.map(x -> x, List.filter(x -> threshold > x, %s)))");
        List<String> differing = new ArrayList<>();
        for (String total : totals) {
            List<Object> plain = visitsClaimed(
                    readFlagged(total.formatted(TWO_NUMBERS.get("as written"))).interactions());
            if (plain.isEmpty()) {
                differing.add(total + ": claims nothing as written");
            }
            TWO_NUMBERS.forEach((way, list) -> {
                CoverageRead.Read read = readFlagged(total.formatted(list));
                if (!plain.equals(visitsClaimed(read.interactions()))
                        || !read.notJoined().isEmpty()) {
                    differing.add(total + " " + way + ": " + visitsClaimed(read.interactions())
                            + " " + read.notJoined());
                }
            });
        }
        assertEquals(List.of(), differing);
    }

    /**
     * A choice is made where it is written, and handing its value on through more closures is no
     * more evaluations of it: a value passed through is made where it was made, and a value a
     * closure makes is made by each application of that closure.
     */
    @Test
    void handingAChoiceOnThroughMoreClosuresChangesNoDecisionCount() {
        String writes = "List.flatMap(r -> { let chosen = if r.active then 1 else 0\n"
                + "    [ chosen, chosen ] }, %s)";
        for (int layers = 0; layers < 3; layers++) {
            for (String handed : List.of("List.flatMap(x -> [ x ], %s)", "List.map(x -> x, %s)")) {
                String once = writes.formatted("[ first ]");
                String twice = writes.formatted("[ first, second ]");
                for (int layer = 0; layer < layers; layer++) {
                    once = handed.formatted(once);
                    twice = handed.formatted(twice);
                }
                assertEquals(List.of(), readFlagged("List.sum(" + once + ")").notJoined(),
                        layers + " layers of " + handed + ", one application");
                assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ),
                        readFlagged("List.sum(" + twice + ")").notJoined(),
                        layers + " layers of " + handed + ", two applications");
            }
        }
    }

    /**
     * A choice written once in an application and used twice there is one decision, and the same
     * written in two applications is two: what is counted is the evaluations of the choice, and
     * not the occurrences of its value.
     */
    @Test
    void aChoiceUsedTwiceInOneApplicationIsOneDecision() {
        String writes = "List.sum(List.flatMap(r -> { let chosen = if %s then 1 else 0\n"
                + "    [ chosen, chosen ] }, %s))";

        for (String condition : List.of("r.active", "flag")) {
            assertEquals(List.of(), readFlagged(writes.formatted(condition, "[ first ]"))
                    .notJoined(), condition + " in one application");
            assertEquals(List.of(WhyNotJoined.A_VALUE_CHOICE_NOT_READ), readFlagged(
                    writes.formatted(condition, "[ first, second ]")).notJoined(),
                    condition + " in two");
        }
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
