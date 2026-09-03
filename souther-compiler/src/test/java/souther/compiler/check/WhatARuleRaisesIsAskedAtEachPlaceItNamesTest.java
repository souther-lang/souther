package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.query.Scopes;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What a rule raises is settled at each place it names, and a place it settled keeps its answer.
 *
 * <p>One clause reaches several names and the reading gets a different distance at each: it takes
 * one in whole, leaves another's line to be worked out, and finds a third states nothing about a
 * line at all. Answered for the clause, the name that was read loses the obligation it raises
 * because a name beside it was not — a question the model asks, dropped because this compiler could
 * not finish reading somewhere else.
 *
 * <p>Written as a model rather than found in one. No model this repository carries conjoins clauses
 * that way, and what is being held is the shape of the answer rather than anything about those
 * models: a producer that settles a clause once and hands the same answer to every name it writes
 * passes over the corpora and fails here.
 */
class WhatARuleRaisesIsAskedAtEachPlaceItNamesTest {

    /**
     * Three conjuncts of one clause, each reaching a different distance.
     *
     * <p>{@code lo >= 1} is a bound this compiler folds, so where the values at {@code lo} stop is
     * a question it raises and answers. {@code hi <= 10 * 2} states where the values at {@code hi}
     * stop and this could not fold the number, so the line is raised and stands. {@code
     * Decimal.compare(a.value, b.value) <= 0} speaks of what an operation answered, so whether it
     * bounds {@code a} or {@code b} is what nothing worked out — and which values may stand at
     * either is a question the model asks regardless.
     */
    private static final String SOURCE = """
            module example.mixed

            data Money = Decimal

            data Span =
                { lo: Int
                , hi: Int
                , a: Money
                , b: Money
                }
                invariant said = lo >= 1
                       && hi <= 10 * 2
                       && Decimal.compare(a.value, b.value) <= 0

            data Taken

            behavior take : (s: Span) -> Taken
            """;

    /**
     * Each name with what the one clause leaves there, in the words the vocabulary uses.
     *
     * <p>Every name it writes appears, because a rule cannot cost a name it does not write and
     * every name it does write is asked both questions.
     */
    @Test
    void oneClauseLeavesADifferentAnswerAtEachNameItNames() {
        Map<String, String> said = new TreeMap<>();
        for (Requirement each : raised().requirements()) {
            switch (each) {
                case Requirement.Determined it -> said.merge(placeOf(it.owed()),
                        askedOf(it.owed()), (had, more) -> had + " " + more);
                case Requirement.BoundaryUndetermined it -> said.merge(it.at().toString(),
                        CoverageObligation.BOUNDARY + "?", (had, more) -> had + " " + more);
            }
        }

        Map<String, String> expected = new LinkedHashMap<>();
        expected.put("lo", "ADMITTED_VALUES BOUNDARY");
        expected.put("hi", "ADMITTED_VALUES BOUNDARY");
        expected.put("a", "ADMITTED_VALUES BOUNDARY?");
        expected.put("b", "ADMITTED_VALUES BOUNDARY?");
        assertEquals(new TreeMap<>(expected), said,
                "a name whose line was worked out keeps it, whatever the name beside it left");
    }

    /** And what is worked out and what is not are told apart rather than counted together. */
    @Test
    void whatWasWorkedOutIsNotAmongWhatWasNot() {
        Set<String> asked = new TreeSet<>();
        raised().obligations().forEach(each -> asked.add(askedOf(each) + " at " + placeOf(each)));
        Set<String> open = new TreeSet<>();
        raised().undetermined()
                .forEach(each -> open.add(CoverageObligation.BOUNDARY + " at " + each.at()));

        assertEquals(new TreeSet<>(Set.of("ADMITTED_VALUES at lo", "ADMITTED_VALUES at hi",
                        "ADMITTED_VALUES at a", "ADMITTED_VALUES at b",
                        "BOUNDARY at lo", "BOUNDARY at hi")),
                asked, "the questions this reading worked out");
        assertEquals(new TreeSet<>(Set.of("BOUNDARY at a", "BOUNDARY at b")), open,
                "and the ones it did not, which are no part of the first");
    }

    /** Which name an obligation is about, as the value raising it spells it. */
    private static String placeOf(Owed owed) {
        return switch (owed) {
            case Owed.AdmittedValues it -> it.path().toString();
            case Owed.Boundary it -> it.on().position().toString();
        };
    }

    /** And which question it is. */
    private static String askedOf(Owed owed) {
        return switch (owed) {
            case Owed.AdmittedValues _ -> CoverageObligation.ADMITTED_VALUES.name();
            case Owed.Boundary _ -> CoverageObligation.BOUNDARY.name();
        };
    }

    /** What the one clause of {@code Span} raises there. */
    private static Required raised() {
        Compilation compilation = Compilation.ofSource(SOURCE, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        assertNotNull(symbols);
        TypeSymbol.AtModule named = TypeSymbols.declared(new TypeKey(module, "Span"));
        Hir.Data data = (Hir.Data) symbols.declaredNode(named.key());
        assertNotNull(data, "no `Span` declared");
        Collection<Required> every = FieldDomains
                .of(named, data, RuleReadings.of(compilation, module),
                        ReadAs.THE_COMPILATION_DOES).required().values();
        assertEquals(1, every.size(), "one clause, so one answer about what it raises");
        return every.iterator().next();
    }
}
