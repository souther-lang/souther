package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code match} standing where a value is handed is one of its arms, read once with each of them
 * standing there (spec §invariant-discharge-terms).
 *
 * <p>An {@code if} in that position was opened already and a {@code match} was not, so what one
 * answered was an atom nothing was recorded against: a construction downstream of it was owed
 * whatever the arms were written as, and whatever the type of the value they answered declared. A
 * helper is how the case is met — a {@code let} whose body is a {@code match} is expanded at the
 * call, so what stands at the parameter is the {@code match}, which is why this reads as "the
 * invariant of a helper's answer is not assumed" and is neither about helpers nor about answers.
 *
 * <p>Both directions. Every silent case here has a neighbour differing in one thing that is not
 * silent, because silence is also what a reading that never ran looks like.
 */
class AMatchHandedAsAValueIsReadWithEachArmStandingThereTest {

    private static final String TYPES = """
            module demo

            data Yen = Int
                invariant nonNeg = value >= 0

            data Loose = Int

            data Big = Int
                invariant big = value >= 1000

            data Fast
            data Slow
            data Plan = Fast | Slow

            data Ranged = Int
                invariant lo = value >= 10
                invariant hi = value <= 100

            data Cheap
            data Dear
            data Fair
            data Grade = Cheap | Dear | Fair

            data Metered = { rate: Yen, slack: Loose }
            data Flat
            data Tariff = Metered | Flat

            let asBig   (a: Yen)  : Big = Big(a.value)
            let twice   (a: Yen)  : Yen = Yen(a.value * 2)
            let twiceOf (l: Loose): Yen = Yen(l.value * 2)
            """;

    private static java.util.List<souther.compiler.diag.Diagnostic> unproven(String body) {
        return Compiler.compileWithWarnings(TYPES + "\n" + body).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code())).toList();
    }

    private static boolean owed(String body) {
        return !unproven(body).isEmpty();
    }

    /** A match of three arms answering a number each, which is the shape the readings are folded
     * over — two of them were all a fold taken two at a time would have reached. */
    private static String grade(String cheap, String dear, String fair) {
        return "let grade (g: Grade): Int =\n    match g with\n"
                + "        | Cheap -> " + cheap + "\n"
                + "        | Dear -> " + dear + "\n"
                + "        | Fair -> " + fair + "\n";
    }

    /** Both arms are numbers written out, and both are above the clause's own end. */
    @Test
    void aMatchOverWrittenNumbersIsTheArmsItIsWrittenWith() {
        assertFalse(owed("""
                behavior charge : (p: Plan) -> Big
                    constructs Big, Yen
                let charge (p) = asBig(match p with | Fast -> Yen(4500) | Slow -> Yen(3500))
                """), "whichever arm ran, what it answered is a number at or above the clause's end");
    }

    /** The same match with one arm below the clause, so what discharged the one above was the arms
     * and not the shape of the expression. */
    @Test
    void aMatchWithAnArmBelowTheClauseIsOwed() {
        assertTrue(owed("""
                behavior charge : (p: Plan) -> Big
                    constructs Big, Yen
                let charge (p) = asBig(match p with | Fast -> Yen(4500) | Slow -> Yen(10))
                """), "one of the arms answers ten, and ten is not at or above a thousand");
    }

    /** What the arms answer carries the rules of its own type, which is what a value handed to a
     * helper's parameter had stopped doing. */
    @Test
    void whatTheArmsAnswerCarriesTheRulesOfItsType() {
        assertFalse(owed("""
                behavior use : (a: Yen, p: Plan) -> Yen
                    constructs Yen
                let use (a, p) = twice(match p with | Fast -> a | Slow -> a)
                """), "whichever arm ran, what it answered is a `Yen`, and a `Yen` is at or above nought");
    }

    /** The same match over a value of a type that declares nothing, so what discharged the one above
     * was the type's rule and not the arms being alike. */
    @Test
    void aMatchOverAValueNothingBoundsIsOwed() {
        assertTrue(owed("""
                behavior use : (l: Loose, p: Plan) -> Yen
                    constructs Yen
                let use (l, p) = twiceOf(match p with | Fast -> l | Slow -> l)
                """), "a `Loose` is any number there is, and twice one of those may be below nought");
    }

    /** The case an author writes: a helper whose body is a match, called where its answer is built
     * from. The expansion puts the match at the parameter, so this is the same reading as above. */
    @Test
    void aHelperWhoseBodyIsAMatchIsThatMatchWhereItIsCalled() {
        assertFalse(owed("""
                let monthly (p: Plan): Yen =
                    match p with
                        | Fast -> Yen(4500)
                        | Slow -> Yen(3500)

                behavior charge : (p: Plan) -> Big
                    constructs Big, Yen
                let charge (p) = asBig(monthly(p))
                """), "the helper answers one of two numbers, and both are above the clause's end");
    }

    @Test
    void aHelperWhoseMatchHasAnArmBelowTheClauseIsOwed() {
        assertTrue(owed("""
                let monthly (p: Plan): Yen =
                    match p with
                        | Fast -> Yen(4500)
                        | Slow -> Yen(10)

                behavior charge : (p: Plan) -> Big
                    constructs Big, Yen
                let charge (p) = asBig(monthly(p))
                """), "the helper answers ten down one of its arms");
    }

    /** An arm's binding is in scope for its body and stands for the value the arm opened, so a field
     * read off it carries what that field's type declares. */
    @Test
    void whatAnArmBindsIsInScopeForItsBody() {
        assertFalse(owed("""
                behavior use : (a: Yen, t: Tariff) -> Yen
                    constructs Yen
                let use (a, t) = twice(match t with | Metered as m -> m.rate | Flat -> a)
                """), "the arm answers a `Yen` field of what it opened");
    }

    /** The same arm answering the field beside it, which its type says nothing about. */
    @Test
    void anArmAnsweringAFieldNothingBoundsIsOwed() {
        assertTrue(owed("""
                behavior use : (l: Loose, t: Tariff) -> Yen
                    constructs Yen
                let use (l, t) = twiceOf(match t with | Metered as m -> m.slack | Flat -> l)
                """), "`slack` is a `Loose`, and twice one of those may be below nought");
    }

    /** What the match asks is read where it stands, so a construction written in the scrutinee is
     * judged like any other. */
    @Test
    void aConstructionWrittenInTheScrutineeIsOwedWhereItIsUnproven() {
        assertTrue(owed("""
                let tariffOf (y: Yen): Tariff = Metered { rate = y, slack = Loose(0) }

                behavior use : (a: Yen, n: Int) -> Yen
                    constructs Yen, Loose, Metered
                let use (a, n) =
                    twice(match tariffOf(Yen(n)) with | Metered as m -> m.rate | Flat -> a)
                """), "`Yen(n)` is written in the scrutinee and nothing bounds `n`");
    }

    /** The same scrutinee built from a number written out, so what was reported above was the
     * construction in the scrutinee and not the scrutinee being a call. */
    @Test
    void aScrutineeBuiltFromAWrittenNumberIsNotOwed() {
        assertFalse(owed("""
                let tariffOf (y: Yen): Tariff = Metered { rate = y, slack = Loose(0) }

                behavior use : (a: Yen) -> Yen
                    constructs Yen, Loose, Metered
                let use (a) =
                    twice(match tariffOf(Yen(4500)) with | Metered as m -> m.rate | Flat -> a)
                """), "four thousand five hundred is at or above nought");
    }

    /** Every arm is read, not the first two. What the readings find is folded, and a fold is what
     * lets a split of any width be said once. */
    @Test
    void everyArmOfAMatchOfMoreThanTwoIsRead() {
        assertFalse(owed(grade("50", "60", "70") + """
                behavior use : (g: Grade) -> Ranged
                    constructs Ranged
                let use (g) = Ranged(grade(g))
                """), "three arms, and every one of them is between ten and a hundred");
    }

    /** The one below the clause is the last arm, which is the one a fold that stopped at two would
     * have dropped. */
    @Test
    void anArmBelowTheClauseIsSaidWhereverItStands() {
        assertTrue(owed(grade("50", "60", "5") + """
                behavior use : (g: Grade) -> Ranged
                    constructs Ranged
                let use (g) = Ranged(grade(g))
                """), "the last arm answers five, and five is not at or above ten");
    }

    /** Two arms leaving two different clauses unsettled leave both of them unsettled: a clause one
     * reading did not establish is one the construction is owed, whichever reading that was. */
    @Test
    void whatDifferentArmsLeaveUnsettledIsSaidTogether() {
        var found = unproven(grade("5", "500", "50") + """
                behavior use : (g: Grade) -> Ranged
                    constructs Ranged
                let use (g) = Ranged(grade(g))
                """);
        assertEquals(1, found.size(), "one construction, said once");
        String unsettled = String.valueOf(found.get(0).values().get("unsettled"));
        assertTrue(unsettled.contains("lo") && unsettled.contains("hi"),
                "the low arm and the high arm each leave a clause standing, and it was `"
                        + unsettled + "`");
    }
}
