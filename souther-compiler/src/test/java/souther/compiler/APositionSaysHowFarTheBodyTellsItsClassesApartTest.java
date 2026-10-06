package souther.compiler;

import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.meta.ModulePath;
import souther.compiler.partition.BodyDistinction;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.ReaderDisposition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A position holding more classes than the behavior's body tells apart says both.
 *
 * <p>The cases of a sum are classes of the position whether or not the body looks at them. So a
 * behavior may take five cases and decide one two-way question with them: every measure over the
 * position comes back full, and the combinations those classes take part in stay unknown, because
 * no row can reach a combination the model has and the behavior never tells apart. A reader handed
 * that count and nothing else reads it as work owed and writes a row that buys a combination and no
 * evidence.
 *
 * <p><b>What the body tells apart.</b> A sum's cases are classes because of the type, so a
 * {@code match} over them composes none of them and tells every one apart. And what is told apart is
 * groups of classes: an arm written for two cases out of four leaves those two together.
 *
 * <p>Neither is a finding and no row answers either. Whether to narrow the input, split the
 * behavior, or leave it as a value this one passes through is the author's, and this compiler knows
 * none of it: what it can say is what it worked out.
 */
class APositionSaysHowFarTheBodyTellsItsClassesApartTest {

    /**
     * Five cases the body never asks about, and a line drawn somewhere else.
     *
     * <p>The strongest form of the shape: the body tells none of the position's classes apart.
     */
    @Test
    void aSumTheBodyNeverLooksAtIsToldApartByNothing() {
        String human = report("""
                module example.untouched

                data TooShort
                data TooLong
                data WrongCase
                data Repeated
                data Banned
                data Refusal = TooShort | TooLong | WrongCase | Repeated | Banned

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);

        assertTrue(human.contains("why holds 5 classes and this behavior does not tell them apart"),
                () -> "the cases are classes and the body looks at none of them: " + human);
    }

    /**
     * And one the body cuts where it is divided says nothing.
     *
     * <p>The half without which the line above would be one this report writes about every
     * position: a number cut by the body's own comparison has as many classes as the comparison
     * tells apart, and there is nothing here for an author to weigh.
     */
    @Test
    void aNumberTheBodyCutsWhereItIsDividedSaysNothing() {
        String human = report("""
                module example.composed

                data Ok = { n: Int }

                behavior judge : (n: Int) -> Ok
                    constructs Ok

                let judge (n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (5)  -> Ok { n = 0 }
                    | (50) -> Ok { n = 1 }
                """);

        assertFalse(human.contains(" classes and this behavior "),
                () -> "the body tells apart what the position is divided into: " + human);
    }

    /**
     * And what it tells apart there is read, and not left unread.
     *
     * <p>The comparison draws a line on the number and parts its values there, and both are the one
     * rule the decision is a reading of. Left unread, every number a body compares would be one
     * nothing is said about.
     */
    @Test
    void aNumberTheBodyComparesIsReadAsToldApartByTheComparison() {
        var compilation = compiled("""
                module example.compared

                data Ok = { n: Int }

                behavior judge : (n: Int) -> Ok
                    constructs Ok

                let judge (n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (5)  -> Ok { n = 0 }
                """);
        var partition = compilation.db()
                .ask(new Adequacy.Coverage("example.compared")).value().get("judge");
        PartitionEvidence.AxisCoverage n = partition.axes().getFirst();

        assertInstanceOf(BodyDistinction.Drawn.class, n.toldApart(), () -> "at " + n);
        assertEquals(2, ((BodyDistinction.Drawn) n.toldApart()).groups().size(), () -> "at " + n);
    }

    /**
     * A comparison made under another tells apart only the values the first let through.
     *
     * <p>The second guard is made of values above zero and comes out the same way for all of them,
     * which the reading of the input finds and draws no line for. So the number is two classes and
     * the body tells both apart — and the second comparison, with no line to place it by, is read as
     * what it is: one that sends every value arriving at it the same way, and not one this compiler
     * could not read.
     */
    @Test
    void aComparisonUnderAnotherTellsApartOnlyWhatTheFirstLetThrough() {
        assertEquals(2, groupsAt("n", toldApartIn("""
                module example.nested

                data Ok = { n: Int }

                behavior judge : (n: Int) -> Ok
                    constructs Ok

                let judge (n) = {
                    guard n > 0 else Ok { n = 0 }
                    guard n > -10 else Ok { n = 1 }
                    Ok { n = 2 }
                }

                example judge
                    | (5) -> Ok { n = 2 }
                """, "example.nested"), 2));
    }

    /**
     * What a way says about a position is what all of its decisions admit there together.
     *
     * <p>Inside the arm for {@code A} or {@code B}, the arm for {@code B} or {@code C} is taken by
     * {@code B} alone, and the one for {@code A} or {@code D} by {@code A} alone. {@code C} and
     * {@code D} both go the outer way round and are never told apart; read one decision at a time,
     * the inner arms would split them.
     */
    @Test
    void whatAWaySaysIsWhatAllOfItsDecisionsAdmitTogether() {
        assertEquals(3, groupsAt("k", toldApartIn("""
                module example.together

                data A
                data B
                data C
                data D
                data Kind = A | B | C | D

                data Ok = { n: Int }

                behavior judge : (k: Kind) -> Ok
                    constructs Ok

                let judge (k) =
                    match k with
                        | A | B ->
                            match k with
                                | B | C -> Ok { n = 1 }
                                | A | D -> Ok { n = 2 }
                        | C | D -> Ok { n = 3 }

                example judge
                    | (A) -> Ok { n = 2 }
                """, "example.together"), 4));
    }

    /**
     * A decision past an attempted construction is made of the values the way to the attempt let
     * through.
     *
     * <p>No way in to the inner {@code match} is named, since which way the attempt goes is nothing
     * a class says. What the outer arm let through is known there all the same — only {@code C} or
     * {@code D} arrives — so the inner arms for {@code A} and {@code B} are taken by no run and the
     * body tells {@code A} from {@code B} nowhere. Read without what the outer arm settled, they
     * would split the two.
     */
    @Test
    void aDecisionPastAnAttemptIsMadeOfWhatTheWayToItLetThrough() {
        assertEquals(3, groupsAt("k", toldApartIn("""
                module example.pastattempt

                data A
                data B
                data C
                data D
                data Kind = A | B | C | D

                data Note = String
                    invariant String.length(value) >= 1
                data NoNote

                data Ok = { n: Int }

                behavior judge : (k: Kind, text: String) -> Ok | NoNote
                    constructs Ok, Note

                let judge (k, text) =
                    match k with
                        | A | B -> Ok { n = 1 }
                        | C | D -> {
                            guard Note(text) as note else NoNote
                            match k with
                                | A -> Ok { n = 2 }
                                | B -> Ok { n = 3 }
                                | C -> Ok { n = 4 }
                                | D -> Ok { n = 5 }
                        }

                example judge
                    | (A, "a") -> Ok { n = 1 }
                """, "example.pastattempt"), 4));
    }

    /**
     * A sum every case of which a {@code match} has an arm for is told apart in full.
     *
     * <p>The match composes no class — the cases are classes because of the type — and tells both
     * cases apart, so the position is not taken wider than it separates, and a combination the rows
     * miss is one they happen not to sit in.
     */
    @Test
    void aSumEveryCaseOfWhichIsMatchedIsToldApartInFull() {
        String model = """
                module example.matched

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Ok = { n: Int }

                behavior judge : (r: Request, n: Int) -> Ok
                    constructs Ok

                let judge (r, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match r with
                        | Draft -> Ok { n = 1 }
                        | Submitted -> Ok { n = 2 }
                }

                example judge
                    | (Draft, 5)      -> Ok { n = 0 }
                    | (Draft, 50)     -> Ok { n = 1 }
                    | (Submitted, 50) -> Ok { n = 2 }
                """;
        String human = report(model);
        var partition = compiled(model).db()
                .ask(new Adequacy.Coverage("example.matched")).value().get("judge");

        // The rows leave a combination of the two positions unknown, so the line is raised for any
        // position here the body tells apart less than in full.
        assertTrue(partition.pairs().space().stream().anyMatch(p -> partition.pairs().unknown(p) > 0),
                () -> "a combination the rows do not sit in: " + partition.pairs());
        assertFalse(human.contains(" classes and this behavior "),
                () -> "a match over every case tells every case apart: " + human);
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "nothing is taken wider than the body tells apart: " + partition.axes());
    }

    /**
     * And so is one matched past an attempted construction.
     *
     * <p>Which way an attempt goes is whether the value's own rules held, which no class of an input
     * names, so no way in to anything after it is stated. The {@code match} after it is still a
     * decision the body makes about the position, and tells both cases apart.
     */
    @Test
    void aSumMatchedPastAnAttemptedConstructionIsToldApartInFull() {
        String model = """
                module example.attempted

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Note = String
                    invariant String.length(value) >= 1
                data NoNote

                data Ok = { n: Int }

                behavior judge : (r: Request, text: String, n: Int) -> Ok | NoNote
                    constructs Ok, Note

                let judge (r, text, n) = {
                    guard Note(text) as note else NoNote
                    guard n > 10 else Ok { n = 0 }
                    match r with
                        | Draft -> Ok { n = 1 }
                        | Submitted -> Ok { n = 2 }
                }

                example judge
                    | (Draft, "a", 5)      -> Ok { n = 0 }
                    | (Draft, "a", 50)     -> Ok { n = 1 }
                    | (Submitted, "a", 50) -> Ok { n = 2 }
                """;
        String human = report(model);
        var partition = compiled(model).db()
                .ask(new Adequacy.Coverage("example.attempted")).value().get("judge");

        assertTrue(partition.pairs().space().stream().anyMatch(p -> partition.pairs().unknown(p) > 0),
                () -> "a combination the rows do not sit in: " + partition.pairs());
        assertFalse(human.contains("r holds"),
                () -> "a match past an attempt tells every case apart: " + human);
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "nothing is taken wider than the body tells apart: " + partition.axes());
    }

    /**
     * But a {@code match} no run reaches tells nothing apart.
     *
     * <p>The inner arm for {@code Yes} is under the outer arm for {@code No}, so no run takes it, and
     * the {@code match} on {@code r} there is no decision the body makes. Read as one, it would say
     * the body tells {@code r} apart when every run treats its cases alike.
     */
    @Test
    void aMatchNoRunReachesTellsNothingApart() {
        String human = report("""
                module example.unreached

                data Yes
                data No
                data Flag = Yes | No

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Ok = { n: Int }

                behavior judge : (f: Flag, r: Request, n: Int) -> Ok
                    constructs Ok

                let judge (f, r, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match f with
                        | Yes -> Ok { n = 1 }
                        | No ->
                            match f with
                                | Yes ->
                                    match r with
                                        | Draft -> Ok { n = 2 }
                                        | Submitted -> Ok { n = 3 }
                                | No -> Ok { n = 4 }
                }

                example judge
                    | (Yes, Draft, 5)  -> Ok { n = 0 }
                    | (Yes, Draft, 50) -> Ok { n = 1 }
                    | (No, Draft, 50)  -> Ok { n = 4 }
                """);

        assertTrue(human.contains("r holds 2 classes and this behavior does not tell them apart"),
                () -> "a match no run reaches is no decision the body makes: " + human);
    }

    /**
     * Nor does one past an attempted construction, where no run reaches the attempt.
     *
     * <p>Past an attempt no way in is stated, which is no reason to forget that no run got to the
     * attempt in the first place: a way in nothing states is still held to what holds above it.
     */
    @Test
    void aMatchPastAnAttemptNoRunReachesTellsNothingApart() {
        String human = report("""
                module example.unreachedattempt

                data Yes
                data No
                data Flag = Yes | No

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Note = String
                    invariant String.length(value) >= 1
                data NoNote

                data Ok = { n: Int }

                behavior judge : (f: Flag, r: Request, text: String, n: Int) -> Ok | NoNote
                    constructs Ok, Note

                let judge (f, r, text, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match f with
                        | Yes -> Ok { n = 1 }
                        | No ->
                            match f with
                                | Yes -> {
                                    guard Note(text) as note else NoNote
                                    match r with
                                        | Draft -> Ok { n = 2 }
                                        | Submitted -> Ok { n = 3 }
                                }
                                | No -> Ok { n = 4 }
                }

                example judge
                    | (Yes, Draft, "a", 5)  -> Ok { n = 0 }
                    | (Yes, Draft, "a", 50) -> Ok { n = 1 }
                    | (No, Draft, "a", 50)  -> Ok { n = 4 }
                """);

        assertTrue(human.contains("r holds 2 classes and this behavior does not tell them apart"),
                () -> "a match past an attempt no run reaches is no decision: " + human);
    }

    /**
     * Nor one inside a function value, where no run reaches the function.
     *
     * <p>The body of a block runs where something calls it, which no way in states, and it is still
     * held to what holds where the block is made.
     */
    @Test
    void aMatchInsideAFunctionNoRunReachesTellsNothingApart() {
        String human = report("""
                module example.unreachedblock

                data Yes
                data No
                data Flag = Yes | No

                data Draft
                data Submitted
                data Request = Draft | Submitted

                data Ok = { n: Int }

                behavior judge : (f: Flag, r: Request, xs: List<Int>, n: Int) -> Ok
                    constructs Ok

                let judge (f, r, xs, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match f with
                        | Yes -> Ok { n = 1 }
                        | No ->
                            match f with
                                | Yes -> Ok { n = List.length(List.filter(x ->
                                    match r with
                                        | Draft -> true
                                        | Submitted -> false, xs)) }
                                | No -> Ok { n = 4 }
                }

                example judge
                    | (Yes, Draft, [1], 5)  -> Ok { n = 0 }
                    | (Yes, Draft, [1], 50) -> Ok { n = 1 }
                    | (No, Draft, [1], 50)  -> Ok { n = 4 }
                """);

        assertTrue(human.contains("r holds 2 classes and this behavior does not tell them apart"),
                () -> "a match in a function no run reaches is no decision: " + human);
    }

    /**
     * A condition is counted by the ways of it a run takes, and not by every way it has.
     *
     * <p>Inside the arm for {@code C} or {@code D} the inner condition is true for {@code C} and
     * false for {@code D}; its ways through {@code A} and {@code B} are ruled out by the arm. Counted
     * whole, they would tell {@code A} from {@code B}, which the body treats alike.
     */
    @Test
    void aConditionIsCountedByTheWaysOfItARunTakes() {
        String human = report("""
                module example.someways

                data A
                data B
                data C
                data D
                data Kind = A | B | C | D

                data Ok = { n: Int }

                behavior judge : (k: Kind, n: Int) -> Ok
                    constructs Ok

                let judge (k, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match k with
                        | A | B -> Ok { n = 1 }
                        | C | D ->
                            if (match k with
                                    | A -> true
                                    | C -> true
                                    | B -> false
                                    | D -> false)
                            then Ok { n = 2 } else Ok { n = 3 }
                }

                example judge
                    | (A, 5)  -> Ok { n = 0 }
                    | (A, 50) -> Ok { n = 1 }
                    | (C, 50) -> Ok { n = 2 }
                """);

        assertTrue(human.contains("k holds 4 classes and this behavior tells them apart as 3 groups"),
                () -> "A and B go one way wherever a run takes them: " + human);
    }

    /**
     * And a value meeting another is counted by the outcomes a run reaching the meeting can have.
     *
     * <p>The sum inside the arm for {@code C} or {@code D} is a meeting of two values, one of them
     * settled by a {@code match} on {@code k}. That value's outcomes through {@code A} and
     * {@code B} are ruled out by the arm, and counted they would tell the two apart.
     */
    @Test
    void aMeetingIsCountedByTheOutcomesARunReachingItCanHave() {
        String human = report("""
                module example.meeting

                data A
                data B
                data C
                data D
                data Kind = A | B | C | D

                data Ok = { n: Int }

                behavior judge : (k: Kind, n: Int) -> Ok
                    constructs Ok

                let judge (k, n) = {
                    guard n > 10 else Ok { n = 0 }
                    match k with
                        | A | B -> Ok { n = 1 }
                        | C | D ->
                            Ok { n = (match k with
                                        | A -> 1
                                        | B -> 2
                                        | C -> 3
                                        | D -> 4)
                                    + (if n > 20 then 10 else 0) }
                }

                example judge
                    | (A, 5)  -> Ok { n = 0 }
                    | (A, 50) -> Ok { n = 1 }
                    | (C, 50) -> Ok { n = 13 }
                """);

        assertTrue(human.contains("k holds 4 classes and this behavior tells them apart as 3 groups"),
                () -> "A and B go one way wherever a run takes them: " + human);
    }

    /**
     * An arm written for several cases leaves them in one group.
     *
     * <p>Four cases and two arms, each for two of them. The body tells the four apart as two groups,
     * and the line says so.
     *
     * <p>Matched twice the same way, so that what is counted is groups and not arms: four arms over
     * the position still leave its cases in two groups.
     */
    @Test
    void anArmForSeveralCasesLeavesThemInOneGroup() {
        String human = report("""
                module example.grouped

                data K1
                data K2
                data K3
                data K4
                data Kind = K1 | K2 | K3 | K4

                data Ok = { n: Int }

                behavior judge : (k: Kind, n: Int) -> Ok
                    constructs Ok

                let judge (k, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = (match k with | K1 | K2 -> 1 | K3 | K4 -> 2)
                            + (match k with | K1 | K2 -> 10 | K3 | K4 -> 20) }
                }

                example judge
                    | (K1, 5)  -> Ok { n = 0 }
                    | (K1, 50) -> Ok { n = 11 }
                    | (K3, 50) -> Ok { n = 22 }
                """);

        assertTrue(human.contains("k holds 4 classes and this behavior tells them apart as 2 groups"),
                () -> "two arms over four cases are two groups: " + human);
    }

    /**
     * And a position the body tells nothing apart about makes no combination to count.
     *
     * <p>A reader shown "some combinations are unknown" writes a row, moves the number by one and
     * buys no evidence with it — and the reason they buy none is that this behavior never tells the
     * position apart. So the space is over what the body says something about, and a position it
     * says nothing about is in none of it: there is no number to read as work.
     *
     * <p>What the reader is told instead is the line above — the position is taken wider than the
     * body tells apart — which is a decision about the model and not a row to write.
     */
    @Test
    void aPositionTheBodyTellsNothingApartMakesNoCombination() {
        String human = report("""
                module example.owed

                data TooShort
                data TooLong
                data WrongCase
                data Refusal = TooShort | TooLong | WrongCase

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);

        assertFalse(human.contains("    combination "),
                () -> "a position this behavior separates none of is in no combination: " + human);
        assertTrue(human.contains("why holds 3 classes and this behavior does not tell them apart"),
                () -> "and what the reader is told is what it takes wider than it separates: "
                        + human);
    }

    /**
     * And what a reader is left with there is a decision, at the position.
     *
     * <p>The report says the two, and what follows from them is that somebody weighs whether this
     * behavior needs the distinction. Not that they narrow anything — a value passed through
     * untouched is as ordinary as an input wider than it needs to be — and not a row, since nobody
     * is owed one at a combination.
     */
    @Test
    void aBehaviorWiderThanItSeparatesLeavesADecisionAtThePosition() {
        var compilation = compiled("""
                module example.left

                data TooShort
                data TooLong
                data WrongCase
                data Refusal = TooShort | TooLong | WrongCase

                data Ok = { n: Int }

                behavior judge : (why: Refusal, n: Int) -> Ok
                    constructs Ok

                let judge (why, n) = {
                    guard n > 10 else Ok { n = 0 }
                    Ok { n = 1 }
                }

                example judge
                    | (TooShort, 5)  -> Ok { n = 0 }
                    | (TooLong, 50)  -> Ok { n = 1 }
                """);
        var partition = compilation.db()
                .ask(new Adequacy.Coverage("example.left")).value().get("judge");

        assertInstanceOf(ReaderDisposition.ReconsiderWhatThisBehaviorNeedsToDistinguish.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "a position it takes wider than it separates: " + partition.pairs());
    }

    /**
     * And where the body tells every position apart in full, nothing further.
     *
     * <p>Without this the arm above would be one this report reaches for whenever a combination is
     * unknown, which is most models: what the rows happen not to sit in is not the same as what
     * they cannot reach.
     */
    @Test
    void combinationsTheRowsMerelyMissLeaveNothingFurther() {
        var compilation = compiled("""
                module example.missed

                data Ok = { n: Int }

                behavior judge : (a: Int, b: Int) -> Ok
                    constructs Ok

                let judge (a, b) = {
                    guard a > 10 else Ok { n = 0 }
                    guard b > 10 else Ok { n = 1 }
                    Ok { n = 2 }
                }

                example judge
                    | (5, 5)   -> Ok { n = 0 }
                    | (50, 50) -> Ok { n = 2 }
                """);
        var partition = compilation.db()
                .ask(new Adequacy.Coverage("example.missed")).value().get("judge");

        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "every position is told apart by the body's own comparisons: "
                        + partition.pairs());
    }

    /**
     * And a position whose own relations the rows all reach is not raised by another's.
     *
     * <p>Three positions, each told apart as two groups of three cases, and what is unknown is
     * between two of them. A position wider than the body tells apart is nothing to weigh where
     * every relation it is in was reached: what makes one worth a reader's time is that some of what
     * it carries is out of every row's reach, and that is a fact about a relation. Read off the
     * space, a position covered throughout would be raised because two others left something
     * unknown.
     */
    @Test
    void aPositionWhoseOwnRelationsAreCoveredIsNotRaisedByAnothers() {
        var compilation = compiled("""
                module example.three

                data A1
                data A2
                data A3
                data As = A1 | A2 | A3

                data B1
                data B2
                data B3
                data Bs = B1 | B2 | B3

                data C1
                data C2
                data C3
                data Cs = C1 | C2 | C3

                data Ok = { n: Int }

                behavior judge : (a: As, b: Bs, c: Cs) -> Ok
                    constructs Ok

                let judge (a, b, c) =
                    Ok { n = (match a with | A1 -> 1 | A2 | A3 -> 0)
                            + (match b with | B1 -> 2 | B2 | B3 -> 0)
                            + (match c with | C1 -> 4 | C2 | C3 -> 0) }

                example judge
                    | (A1, B1, C1) -> Ok { n = 7 }
                    | (A1, B2, C2) -> Ok { n = 1 }
                    | (A1, B3, C3) -> Ok { n = 1 }
                    | (A2, B1, C1) -> Ok { n = 6 }
                    | (A2, B2, C2) -> Ok { n = 0 }
                    | (A2, B3, C3) -> Ok { n = 0 }
                    | (A3, B1, C1) -> Ok { n = 6 }
                    | (A3, B2, C2) -> Ok { n = 0 }
                    | (A3, B3, C3) -> Ok { n = 0 }
                """);
        var partition = compilation.db()
                .ask(new Adequacy.Coverage("example.three")).value().get("judge");
        List<String> raised = ReaderDisposition
                .widerThanTheyAreSeparated(partition.pairs(), partition.axes()).stream()
                .map(each -> each.axis().at().term()).toList();

        // Every relation `a` is in was reached, and `b` and `c` leave one between them unknown.
        assertFalse(raised.contains("a"),
                () -> "every relation `a` takes part in is covered, so it is not raised: "
                        + raised + " over " + partition.pairs());
        assertTrue(raised.contains("b") && raised.contains("c"),
                () -> "the two that leave a relation unknown are raised: " + raised
                        + " over " + partition.pairs());
    }

    /**
     * A behavior with no body is not said to tell nothing apart.
     *
     * <p>What it tells apart is not known: the reading is missing, and nothing about the behavior
     * says it takes a position wider than it needs. Every combination is one a row can be written at
     * and one the rows happen not to sit in.
     */
    @Test
    void aBehaviorWithNoBodyIsNotSaidToTellNothingApart() {
        var compilation = compiled("""
                module example.injected

                data Yes
                data No
                data Flag = Yes | No

                data A1
                data A2
                data A3
                data Wide = A1 | A2 | A3

                data Ok = { n: Int }

                behavior judge : (a: Flag, c: Wide) -> Ok

                example judge
                    | (Yes, A1) -> Ok { n = 0 }
                    | (No, A2)  -> Ok { n = 0 }
                """);
        var partition = compilation.db()
                .ask(new Adequacy.Coverage("example.injected")).value().get("judge");

        assertTrue(partition.pairs().space().stream().anyMatch(p -> partition.pairs().unknown(p) > 0),
                () -> "a combination the rows do not sit in: " + partition.pairs());
        assertInstanceOf(ReaderDisposition.Settled.class,
                ReaderDisposition.of(partition.pairs(), partition.axes()),
                () -> "a behavior with no body is not taken wider than it tells apart: "
                        + partition.axes());
    }

    /**
     * A comparison the body writes where no decision reads it is not read as telling nothing apart.
     *
     * <p>The predicate handed to {@code List.filter} divides the elements into classes, and the walk
     * that finds the decisions does not enter it. What the body tells apart there is real and is not
     * read into classes, so nothing is said about the position — rather than the line saying the
     * body tells none of it apart.
     */
    @Test
    void aComparisonNoDecisionReadsIsNotReadAsTellingNothingApart() {
        String model = """
                module example.filtered

                data Yes
                data No
                data Flag = Yes | No

                data Ok = { n: Int }

                behavior judge : (f: Flag, xs: List<Int>) -> Ok
                    constructs Ok

                let judge (f, xs) =
                    match f with
                        | Yes -> Ok { n = List.length(List.filter(x -> x > 10, xs)) }
                        | No -> Ok { n = 0 }

                example judge
                    | (Yes, [5]) -> Ok { n = 0 }
                    | (No, [50]) -> Ok { n = 0 }
                """;
        String human = report(model);
        var partition = compiled(model).db()
                .ask(new Adequacy.Coverage("example.filtered")).value().get("judge");
        PartitionEvidence.AxisCoverage elements = partition.axes().stream()
                .filter(each -> each.name().equals("xs[*]")).findFirst().orElseThrow(
                        () -> new AssertionError("the predicate divides the elements: "
                                + partition.axes()));

        assertEquals(2, elements.classes().size(),
                () -> "the comparison divides the elements in two: " + elements);
        assertFalse(human.contains("xs[*] holds"),
                () -> "what the predicate tells apart is not read as nothing: " + human);
    }

    /** What the body of {@code module}'s {@code judge} tells apart at each of its positions. */
    private static List<PartitionEvidence.AxisCoverage> toldApartIn(String model, String module) {
        return compiled(model).db().ask(new Adequacy.Coverage(module)).value().get("judge")
                .axes();
    }

    /**
     * How many groups the body tells the classes at {@code name} apart as, having checked that the
     * position holds {@code classes} of them and that what it tells apart was read.
     */
    private static int groupsAt(String name, List<PartitionEvidence.AxisCoverage> axes,
                                int classes) {
        PartitionEvidence.AxisCoverage at = axes.stream()
                .filter(each -> each.name().equals(name)).findFirst()
                .orElseThrow(() -> new AssertionError("no position " + name + " in " + axes));
        assertEquals(classes, at.classes().size(), () -> "the classes at " + name + ": " + at);
        assertInstanceOf(BodyDistinction.Drawn.class, at.toldApart(), () -> "at " + at);
        return ((BodyDistinction.Drawn) at.toldApart()).groups().size();
    }

    private static Compilation compiled(String model) {
        return Compiler.analyzedModules(List.of(model), ModulePath.EMPTY, new ArrayList<>(),
                Adequacy.Asked.fullReport());
    }

    private static String report(String model) {
        List<Located> warnings = new ArrayList<>();
        Compilation compilation = Compiler.analyzedModules(List.of(model), ModulePath.EMPTY,
                warnings, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
