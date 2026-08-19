package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

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

            data Metered = { rate: Yen, slack: Loose }
            data Flat
            data Tariff = Metered | Flat

            let asBig   (a: Yen)  : Big = Big(a.value)
            let twice   (a: Yen)  : Yen = Yen(a.value * 2)
            let twiceOf (l: Loose): Yen = Yen(l.value * 2)
            """;

    private static boolean owed(String body) {
        return Compiler.compileWithWarnings(TYPES + "\n" + body).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
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
}
