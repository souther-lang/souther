package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What one conjunct of a rule was holding is read by asking what the rules leave without it.
 *
 * <p>Every conjunct that placed no end and is about one number, and not the ones naming a value
 * alone. A disequality, an equality and an arithmetic no end could be read from are three ways of
 * leaving a coordinate somewhere without saying where.
 *
 * <p>{@code String.length(value) /= 0} takes the nought away from a length that is never negative,
 * and the position starts at one. Asked of the rules with that conjunct still in them, the answer
 * is that the rule cuts where the quantity does not run — its own effect having already taken the
 * value away.
 *
 * <p>So the reading is asked twice, and what moves between the two is what the conjunct was
 * holding. The floor a clause wrote and the floor the carrier supplies go through it alike: neither
 * is named anywhere in the comparison, and both are in what the other rules leave.
 */
class WhatAConjunctWasHoldingIsReadByLeavingItOutTest {

    /** A length that is never negative, with the nought taken away and nothing else written. */
    @Test
    void aHoleAtTheCarriersOwnFloorMovesIt() {
        assertEquals(List.of(Endpoint.inclusive(Count.of(1))),
                movedBy("""
                        data Subject = String
                            invariant notBlank = String.length(value) /= 0
                        """),
                "the length starts at one, and the rule that took the nought away is what put it"
                        + " there");
    }

    /**
     * The same where a clause wrote the floor instead of the carrier supplying it.
     *
     * <p>Twice, because both clauses hold the end at one: without the denial the values start at
     * nought, and without the floor they stop nowhere. Which is the same answer two clauses saying
     * one thing get anywhere else, and what a population split by end-shape could not give — the
     * clause that wrote a bound is not a candidate for the end it did not place, and the end it did
     * place is at a value the rules refuse.
     */
    @Test
    void aHoleAtAWrittenFloorMovesItAlike() {
        assertEquals(
                List.of(Endpoint.inclusive(Count.of(1)), Endpoint.inclusive(Count.of(1))),
                movedBy("""
                        data Subject = Int
                            invariant notNegative = value >= 0
                            invariant notZero = value /= 0
                        """),
                "one mechanism, and nothing tells the two floors apart");
    }

    /** A hole with values either side of it moves nothing, which is the hole a range cannot keep. */
    @Test
    void aHoleWithSomethingEitherSideOfItMovesNoEnd() {
        assertEquals(List.of(),
                movedBy("""
                        data Subject = Int
                            invariant notZero = value /= 0
                        """),
                "nothing says which side of nought the value is on");
    }

    /** A rule naming a value states both ends at once, and both are its. */
    @Test
    void aRuleNamingAValueMovesBothEnds() {
        assertEquals(List.of(Endpoint.inclusive(Count.of(5)), Endpoint.inclusive(Count.of(5))),
                movedBy("""
                        data Subject = Int
                            invariant exactlyFive = value == 5
                        """),
                "the value stops at five either way");
    }

    /**
     * A rule whose arithmetic no end was read from, which names no coordinate on either side.
     *
     * <p>The same question and the same answer. What it moved is read off the values, and nothing
     * anywhere inverts the {@code 2 *}.
     */
    @Test
    void anArithmeticNoEndWasReadFromMovesAnEndAlike() {
        assertEquals(List.of(Endpoint.inclusive(Count.of(2))),
                movedBy("""
                        data Subject = Int
                            invariant doubled = value * 2 >= 4
                        """),
                "the values start at two, and the rule that put them there is this one");
    }

    /** The ends every conjunct over one coordinate moved, in the order the rules were read. */
    private static List<Endpoint> movedBy(String declaration) {
        FieldDomains read = domainsOf(declaration);
        assertTrue(!read.aboutOneCoordinate().isEmpty(),
                "the model under test writes a rule that placed no end on one number");
        return read.aboutOneCoordinate().stream()
                .flatMap(each -> read.movedEndsOf(each).stream())
                .map(InvariantBound::end)
                .toList();
    }

    private static FieldDomains domainsOf(String declaration) {
        String source = """
                module example.holding

                %s
                data Ok

                behavior take : (n: Subject) -> Ok
                let take (n) = Ok
                """.formatted(declaration);
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        TypeSymbol subject = TypeSymbols.declared(new TypeKey(module, "Subject"));
        return Rules.of(subject, symbols, ReadAs.THE_COMPILATION_DOES).bounds();
    }
}
