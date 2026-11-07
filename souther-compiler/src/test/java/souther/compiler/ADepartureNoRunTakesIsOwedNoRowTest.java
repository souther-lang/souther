package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.DeadBranchMessage;
import souther.compiler.coverage.SourceOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.ArmObligation;
import souther.compiler.query.ArmSummary;
import souther.compiler.query.Compilation;
import souther.compiler.query.Measurement;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An attempted construction's departure is taken where a clause it answers fails, so one whose
 * clauses the conditions above it establish is entered by no run and owed no row.
 *
 * <p>Which departure a run takes is what the construction's clauses come to where the attempt
 * stands, asked by the rules the discharge check reports by. A departure answering a clause that
 * may fail there is owed as it was; so is one answering a clause the check cannot read, which holds
 * nowhere it says.
 */
class ADepartureNoRunTakesIsOwedNoRowTest {

    /** The seats a count is kept beside: a seat taken is a value not in the set, so the set grows
     *  by one and the count falls by one, and the invariant holds wherever the attempt is reached. */
    private static final String SEATS = """
            module seats

            data Seats = { taken: Set<Int>, free: Int, cap: Int }
                invariant Set.size(taken) + free == cap && free >= 0

            behavior take : (s: Seats, n: Int) -> Seats | Already | Full
                constructs Seats
            let take (s, n) = {
                guard Bool.not(Set.contains(n, s.taken)) else Already
                guard s.free > 0 else Full
                guard Seats { ...s, taken = Set.insert(n, s.taken), free = s.free - 1 } as next else Full
                next
            }

            example take
                | (Seats { taken = [], free = 1, cap = 1 }, 0) -> Seats { taken = [0], free = 0, cap = 1 }
                | (Seats { taken = [], free = 2, cap = 2 }, 0) -> Seats { taken = [0], free = 1, cap = 2 }
                | (Seats { taken = [0], free = 0, cap = 1 }, 0) -> Already
                | (Seats { taken = [1], free = 0, cap = 1 }, 0) -> Full
            """;

    @Test
    void theSeatsTakenOweNoRowThroughTheAttemptsDeparture() {
        Compilation compilation = measured(SEATS);
        String report = report(compilation);
        assertFalse(report.contains("no row goes through"), report);
        assertFalse(report.contains("gap marked `!`"), report);
        // Entered by no run, which is what a dead branch is, and taken out by building the value
        // outright.
        assertEquals(List.of("E1327"), codes(compilation));
        assertTrue(compilation.warnings().getFirst().diagnostic().notes().stream()
                        .anyMatch(note -> note.said()
                                instanceof DeadBranchMessage.BuildTheValueRatherThanAttemptIt),
                () -> compilation.warnings().getFirst().diagnostic().notes().toString());
    }

    /** A plain guard nothing reaches is taken out, and not built. */
    @Test
    void aDeadGuardIsStillToldToBeTakenOut() {
        Compilation compilation = measured("""
                module seats

                behavior take : (free: Int) -> Int | Full
                let take (free) = {
                    guard free > 0 else Full
                    guard free - 1 >= 0 else Full
                    free
                }

                example take
                    | (1) -> 1
                    | (0) -> Full
                """);
        assertEquals(List.of("E1327"), codes(compilation));
        assertTrue(compilation.warnings().getFirst().diagnostic().notes().stream()
                .anyMatch(note -> note.said()
                        instanceof DeadBranchMessage.TakeItOutOrLetSomethingReachIt));
    }

    @Test
    void aDepartureTheGuardsAboveShutIsOwedNoRow() {
        Compilation compilation = measured("""
                module seats

                data Seats = { free: Int }
                    invariant free >= 0

                behavior take : (s: Seats) -> Seats | Full
                    constructs Seats
                let take (s) = {
                    guard s.free > 0 else Full
                    guard Seats { free = s.free - 1 } as next else Full
                    next
                }

                example take
                    | (Seats { free = 1 }) -> Seats { free = 0 }
                    | (Seats { free = 0 }) -> Full
                """);
        assertFalse(owesADeparture(compilation, "seats", "take"), () -> report(compilation));
    }

    @Test
    void aDepartureARunCanTakeIsStillOwed() {
        Compilation compilation = measured("""
                module seats

                data Seats = { free: Int }
                    invariant free >= 0

                behavior take : (s: Seats) -> Seats | Full
                    constructs Seats
                let take (s) = {
                    guard Seats { free = s.free - 1 } as next else Full
                    next
                }

                example take
                    | (Seats { free = 1 }) -> Seats { free = 0 }
                """);
        assertTrue(owesADeparture(compilation, "seats", "take"), () -> report(compilation));
    }

    /** Each departure answers the clause it names, so the one whose clause the guard establishes is
     *  shut and the other is still owed. */
    @Test
    void aNamedDepartureIsOwedOnlyWhereItsClauseMayFail() {
        String report = report(measured("""
                module seats

                data TooWide
                data Unordered
                data Window = { lo: Int, hi: Int }
                    invariant ordered = lo <= hi
                    invariant small = hi - lo <= 10

                behavior w : (a: Int, b: Int) -> Window | Unordered | TooWide
                    constructs Window
                let w (a, b) = {
                    guard a <= b else Unordered
                    guard Window { lo = a, hi = b } as win else
                        | ordered -> Unordered
                        | small -> TooWide
                    win
                }

                example w
                    | (1, 2) -> Window { lo = 1, hi = 2 }
                    | (2, 1) -> Unordered
                """));
        assertTrue(report.contains("no row goes through `else small`"), report);
        assertFalse(report.contains("no row goes through `else ordered`"), report);
    }

    private static final String WINDOW = """
            module seats

            data TooWide
            data Unordered
            data Window = { lo: Int, hi: Int }
                invariant ordered = lo <= hi
                invariant small = hi - lo <= 10

            behavior w : (a: Int, b: Int) -> Window | Unordered | TooWide
                constructs Window
            let w (a, b) = {
                guard a <= b else Unordered
                guard Window { lo = a, hi = b } as win else
                    | ordered -> %s
                    | small -> TooWide
                win
            }

            example w
                | (1, 2) -> Window { lo = 1, hi = 2 }
                | (1, 20) -> TooWide
                | (2, 1) -> Unordered
            """;

    /** A departure no run takes beside one a run takes stays, since its clause is answered by a
     *  departure, and says so with `unreachable`; building the value outright would take the
     *  other away. Written so, it is no arm and nothing is said of it. */
    @Test
    void aDepartureShutBesideOneTakenIsAnsweredWithUnreachable() {
        Compilation shut = measured(WINDOW.formatted("Unordered"));
        assertEquals(List.of("E1327"), codes(shut));
        assertEquals(List.of(DeadBranchMessage.AnswerTheDepartureWithUnreachable.class),
                hints(shut));
        Compilation answered = measured(WINDOW.formatted("unreachable \"a <= b is guarded\""));
        assertEquals(List.of(), codes(answered));
        assertFalse(report(answered).contains("no row goes through"), () -> report(answered));
    }

    /** Clauses each of which may hold, and which cannot hold together where the attempt stands:
     *  no run builds the value, so its success branch is owed no row, and the attempt is
     *  answered by what it departs with. */
    @Test
    void anAttemptWhoseClausesCannotHoldTogetherOwesNoRowThroughItsSuccess() {
        Compilation compilation = measured("""
                module pairs

                data Bad
                data Pair = { n: Int, m: Int }
                    invariant left = n > 0
                    invariant right = m > 0

                behavior f : (n: Int) -> Pair | Bad
                    constructs Pair
                let f (n) = {
                    guard Pair { n = n, m = 0 - n } as p else
                        | left -> Bad
                        | right -> Bad
                    p
                }

                example f
                    | (1) -> Bad
                    | (0 - 1) -> Bad
                """);
        assertFalse(owes(compilation, "pairs", "f", SourceOutcome.Held.class),
                () -> report(compilation));
        assertEquals(List.of("E1327"), codes(compilation));
        assertEquals(List.of(DeadBranchMessage.AnswerTheDepartureRatherThanAttemptIt.class),
                hints(compilation));
    }

    /** The control: clauses that hold together somewhere leave the success branch owed. */
    @Test
    void anAttemptWhoseClausesMayHoldTogetherOwesItsSuccess() {
        Compilation compilation = measured("""
                module pairs

                data Bad
                data Pair = { n: Int, m: Int }
                    invariant left = n > 0
                    invariant right = m > 0

                behavior f : (n: Int) -> Pair | Bad
                    constructs Pair
                let f (n) = {
                    guard Pair { n = n, m = n } as p else
                        | left -> Bad
                        | right -> Bad
                    p
                }

                example f
                    | (0) -> Bad
                """);
        assertTrue(owes(compilation, "pairs", "f", SourceOutcome.Held.class),
                () -> report(compilation));
    }

    /** A fork inside a branch nothing enters is reached by nothing either: owed no row, and said
     *  with the branch it is inside, which is what an author takes out. Plain forks and attempts
     *  alike. */
    @Test
    void theForksInsideADeadBranchAreOwedNothingAndSaidWithIt() {
        String model = """
                module counts

                data Count = { n: Int }
                    invariant n >= 0

                data Bad

                behavior f : (n: Int) -> Count | Bad
                    constructs Count
                let f (n) = {
                    guard n > 0 else Bad
                    if n < 0 then {
                        %s
                    } else Count { n = n }
                }

                example f
                    | (1) -> Count { n = 1 }
                    | (0) -> Bad
                """;
        for (String inside : List.of("if n < 0 - 5 then Bad else Count { n = 0 }",
                "guard Count { n = n } as c else Bad\n        c")) {
            Compilation compilation = measured(model.formatted(inside));
            assertFalse(report(compilation).contains("no row goes through"),
                    () -> report(compilation));
            assertEquals(List.of("E1327"), codes(compilation));
            assertEquals(List.of(DeadBranchMessage.TakeItOutOrLetSomethingReachIt.class),
                    hints(compilation));
        }
    }

    /** A branch of a helper said with the branch it is inside at one call, and dead where it is
     *  written at another, is said where it is written: the branch it is inside at the first is
     *  not dead at the second, so nothing else says it. */
    @Test
    void aBranchDeadOnItsOwnAtOneCallIsSaidThoughItIsInsideADeadBranchAtAnother() {
        Compilation compilation = measured("""
                module seats

                data Full

                let lower (f: Int) : Int | Full = {
                    guard f - 1 >= 0 else Full
                    f - 1
                }

                behavior take : (a: Int) -> Int | Full
                let take (a) = {
                    guard a > 0 else Full
                    if a < 0 then lower(a) else lower(a)
                }

                example take
                    | (1) -> 0
                    | (0) -> Full
                """);
        assertEquals(List.of("E1327", "E1327"), codes(compilation));
    }

    /** A clause read on a value the check names nothing of is left to the run-time check, which is
     *  no clause holding. */
    @Test
    void aClauseTheCheckCannotReadLeavesItsDepartureOwed() {
        Compilation compilation = measured("""
                module tags

                data Bad
                data Tag = String
                    invariant prefixed = String.startsWith("A", value)

                behavior f : (s: String) -> Tag | Bad
                    constructs Tag
                let f (s) = {
                    guard Tag(String.trim(s)) as t else Bad
                    t
                }

                example f
                    | ("A") -> Tag("A")
                """);
        assertTrue(owesADeparture(compilation, "tags", "f"), () -> report(compilation));
    }

    /** The tree that runs holds the reversal as the walk it lowers to, and the check reads it as
     *  the operation it is: what the check found of the attempt is what its departure is entered
     *  by. */
    @Test
    void whatTheCheckReadsOfAnOperationShutsTheDepartureAsWell() {
        Compilation compilation = measured("""
                module seats

                data Count = { n: Int }
                    invariant n >= 0

                behavior tally : (xs: List<Int>) -> Count | Negative
                    constructs Count
                let tally (xs) = {
                    guard Count { n = List.length(List.reverse(xs)) } as c else Negative
                    c
                }

                example tally
                    | ([1]) -> Count { n = 1 }
                """);
        assertFalse(owesADeparture(compilation, "seats", "tally"), () -> report(compilation));
    }

    /** What the check found of each copy of an attempt a helper makes is what that copy's
     *  departure is entered by: shut at both calls, it is owed nothing, and shut at one only, it is
     *  owed. */
    @Test
    void whatTheCheckFoundOfEachCopyIsAskedOfThatCopy() {
        String helper = """
                module seats

                data Count = { n: Int }
                    invariant n >= 0

                let less (xs: List<Int>, d: Int) : Count | Negative = {
                    guard Count { n = List.length(List.reverse(xs)) - d } as c else Negative
                    c
                }

                behavior tally : (xs: List<Int>, ys: List<Int>) -> Count | Negative
                    constructs Count
                let tally (xs, ys) = if List.isEmpty(ys) then less(xs, %s) else less(ys, 0)

                example tally
                    | ([1], []) -> Count { n = %s }
                    | ([1], [2]) -> Count { n = 1 }
                """;
        Compilation bothShut = measured(helper.formatted("0", "1"));
        assertFalse(owesADeparture(bothShut, "seats", "tally"), () -> report(bothShut));
        Compilation oneShut = measured(helper.formatted("1", "0"));
        assertTrue(owesADeparture(oneShut, "seats", "tally"), () -> report(oneShut));
    }

    /** A value that is one of two is read once for each, and a departure shut on one of them only
     *  is one the other's runs take. */
    @Test
    void aDepartureShutForOneOfTheValuesBuiltIsStillOwed() {
        Compilation compilation = measured("""
                module seats

                data Count = { n: Int }
                    invariant n >= 0

                behavior pick : (b: Bool) -> Count | Negative
                    constructs Count
                let pick (b) = {
                    guard Count { n = if b then 1 else 0 - 1 } as c else Negative
                    c
                }

                example pick
                    | (true) -> Count { n = 1 }
                """);
        // The value's own `else` is owed a row as well, and says so in the same words; which arm
        // is owed is asked of the arms.
        assertTrue(owesADeparture(compilation, "seats", "pick"), () -> report(compilation));
    }

    /** Whether {@code behavior} owes a row through a departure of an attempted construction. */
    private static boolean owesADeparture(Compilation compilation, String module,
                                          String behavior) {
        return owes(compilation, module, behavior, SourceOutcome.Failed.class);
    }

    /** Whether {@code behavior} owes a row through an arm of an attempted construction whose
     *  outcome is {@code outcome}. */
    private static boolean owes(Compilation compilation, String module, String behavior,
                                Class<? extends SourceOutcome.Arm> outcome) {
        return compilation.db().ask(new Adequacy.BranchCoverage(module)).value().get(behavior)
                .measured() instanceof Measurement.Complete<ArmSummary>(ArmSummary summary)
                && summary.all().stream()
                        .filter(ArmObligation.Counted.class::isInstance)
                        .map(ArmObligation.Counted.class::cast)
                        .flatMap(arm -> arm.occurrences().stream())
                        .anyMatch(site -> outcome.isInstance(site.outcome())
                                && (site.outcome() instanceof SourceOutcome.Failed(
                                        SourceOutcome.FailedBy.Construction _)
                                        || site.outcome() instanceof SourceOutcome.Held(
                                                SourceOutcome.HeldBy.Construction _)));
    }

    /** What each warning says to do about it. */
    private static List<Class<?>> hints(Compilation compilation) {
        return compilation.warnings().stream()
                .flatMap(each -> each.diagnostic().notes().stream())
                .map(note -> (Object) note.said())
                .filter(said -> said instanceof DeadBranchMessage.TakeItOutOrLetSomethingReachIt
                        || said instanceof DeadBranchMessage.BuildTheValueRatherThanAttemptIt
                        || said instanceof DeadBranchMessage.AnswerTheDepartureWithUnreachable
                        || said instanceof DeadBranchMessage.AnswerTheDepartureRatherThanAttemptIt)
                .<Class<?>>map(Object::getClass)
                .toList();
    }

    /** One departure written once and copied at two calls: shut at one call and not at the other
     *  is a departure some run takes. */
    @Test
    void aDepartureShutAtOneCallOfItsHelperOnlyIsStillOwed() {
        Compilation compilation = measured("""
                module seats

                data Seats = { free: Int }
                    invariant free >= 0

                let lower (f: Int) : Seats | Full = {
                    guard Seats { free = f - 1 } as s else Full
                    s
                }

                behavior take : (a: Int, b: Int) -> Seats | Full
                    constructs Seats
                let take (a, b) = {
                    guard a > 0 else Full
                    if b > a then lower(a) else lower(b)
                }

                example take
                    | (2, 5) -> Seats { free = 1 }
                    | (1, 1) -> Seats { free = 0 }
                    | (0, 0) -> Full
                """);
        assertTrue(owesADeparture(compilation, "seats", "take"), () -> report(compilation));
    }

    /** The same departure shut at both calls is one no run takes. */
    @Test
    void aDepartureShutAtEveryCallOfItsHelperIsOwedNoRow() {
        Compilation compilation = measured("""
                module seats

                data Seats = { free: Int }
                    invariant free >= 0

                let lower (f: Int) : Seats | Full = {
                    guard Seats { free = f - 1 } as s else Full
                    s
                }

                behavior take : (a: Int, b: Int) -> Seats | Full
                    constructs Seats
                let take (a, b) = {
                    guard a > 0 else Full
                    if b > a then lower(b) else lower(a)
                }

                example take
                    | (1, 1) -> Seats { free = 0 }
                    | (1, 5) -> Seats { free = 4 }
                    | (0, 0) -> Full
                """);
        assertFalse(owesADeparture(compilation, "seats", "take"), () -> report(compilation));
    }

    private static List<String> codes(Compilation compilation) {
        return compilation.warnings().stream().map(each -> each.diagnostic().code()).toList();
    }

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        return compilation;
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }
}
