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
 * <p>A rule that names a value places no end, and where the value it names sits at an edge of what
 * everything else leaves, it moves that edge: {@code String.length(value) /= 0} takes the nought
 * away from a length that is never negative, and the position starts at one. Asked of the rules
 * with that conjunct still in them, the answer is that the rule cuts where the quantity does not
 * run — its own effect having already taken the value away.
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

    /** The same where a clause wrote the floor instead of the carrier supplying it. */
    @Test
    void aHoleAtAWrittenFloorMovesItAlike() {
        assertEquals(List.of(Endpoint.inclusive(Count.of(1))),
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

    /** The ends every conjunct naming a value moved, in the order the rules were read. */
    private static List<Endpoint> movedBy(String declaration) {
        FieldDomains read = domainsOf(declaration);
        assertTrue(!read.namesAValue().isEmpty(),
                "the model under test writes a rule that names a value");
        return read.namesAValue().stream()
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
