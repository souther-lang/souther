package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.Boundary;
import souther.compiler.check.SumCases;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a value of a sum can be is the compilation's answer, worked out once for the sum, and a
 * reader ordering a value of an enumeration depends on that answer and not on each of its cases.
 *
 * <p>The leaves are read off what every case of the sum is, so a reader working them out for
 * itself pays for every case of the enumeration each time it orders a value of it — once for each
 * product whose field is typed by it, and once more for each question asked of that field. Held
 * by the compilation, the cases are read once.
 *
 * <p>What is held is the readers' own dependencies. The answer for the sum reads what each case is,
 * and has to; what a reader must not do is read it beside that answer, which is what working the
 * leaves out for itself looks like from outside.
 */
class WhatASumCanBeIsAnsweredOnceForTheSumTest {

    private static final String MODULE = "shop";

    /**
     * A product whose invariant orders a field typed by the enumeration, and a behavior ordering a
     * value of it. Neither names {@code Prospecting} or {@code Qualified}: both compare with
     * {@code Won}.
     */
    private static final String SOURCE = """
            module shop

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Ok
            data No
            data Verdict = Ok | No

            data Deal =
                { at: Stage
                }
                invariant early = at < Won

            data Event = Deal | Stage

            behavior advance : (s: Stage) -> Verdict
            let advance (s) = if s < Won then Ok else No
            """;

    private static Compilation compiled(String source) {
        Compilation c = Compilation.ofDocuments(Map.of("shop.sou", source), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");
        return c;
    }

    private static TypeKey key(String name) {
        return new TypeKey(MODULE, name);
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(key(name));
    }

    /** What the product says, what its rules come to, and the behavior's checked body. */
    private static final List<Key<?>> READERS = List.of(
            new Shapes.MeaningOf(key("Deal")),
            new Machines.OfDeclaration(key("Deal")),
            new Bodies.CheckedBehavior(MODULE, "advance"));

    @Test
    void theCompilationAnswersWhatAValueOfTheSumCanBe() {
        Compilation c = compiled(SOURCE);

        SumCases.Cases stage = Shapes.sumCases(c.db()).of(named("Stage"));
        assertInstanceOf(SumCases.Enumeration.class, stage, "every case of Stage is a unit");
        assertEquals(List.of(named("Prospecting"), named("Qualified"), named("Won")), stage.cases());

        SumCases.Cases event = Shapes.sumCases(c.db()).of(named("Event"));
        assertInstanceOf(SumCases.NonEnumeration.class, event, "a case of Event carries fields");
        assertEquals(List.of(named("Deal"), named("Prospecting"), named("Qualified"), named("Won")),
                event.cases(), "and a sum among its cases is its leaves");
    }

    @Test
    void aReaderOrderingAValueOfTheEnumerationDependsOnTheAnswerForIt() {
        Compilation c = compiled(SOURCE);

        for (Key<?> reader : READERS) {
            Set<Key<?>> read = c.db().dependenciesOf(reader);
            assertTrue(read.contains(new Shapes.SumCasesOf(named("Stage"))),
                    () -> reader + " ordered a value of Stage without the compilation's answer: "
                            + read);
        }
    }

    /**
     * Its own dependencies hold nothing about the cases it does not name: what each of them is was
     * read by the answer for the sum. A reader reading it beside the answer is opening the
     * enumeration again.
     *
     * <p>Nor anything else of those cases. Every one of them is a unit, which holds nothing, so a
     * reading of a value of the enumeration that opened each case — what it wraps, what declares
     * it — would find nothing there, and pay for every case of the enumeration to find it.
     */
    @Test
    void aReaderOrderingAValueOfTheEnumerationReadsNoCaseItDoesNotNameBesideTheAnswer() {
        Compilation c = compiled(SOURCE);

        for (Key<?> reader : READERS) {
            Set<Key<?>> read = c.db().dependenciesOf(reader);
            for (String unnamed : List.of("Prospecting", "Qualified")) {
                for (Key<?> ofTheCase : List.<Key<?>>of(new Names.DeclarationKindOf(key(unnamed)),
                        new Names.ResolvedDeclaration(key(unnamed)),
                        new Shapes.NewtypeInnerOf(key(unnamed)),
                        new Shapes.MeaningOf(key(unnamed)))) {
                    assertTrue(read.stream().noneMatch(ofTheCase::equals),
                            () -> reader + " read " + ofTheCase + " beside the answer for Stage: "
                                    + read);
                }
            }
        }
    }

    /**
     * How the enumeration crosses a boundary reads the same answer. That every leaf of it is a
     * unit is the sum's fact and is held there; what is the boundary's is only that such a set is
     * written as a bare tag, so it asks nothing of the cases beside the answer.
     */
    @Test
    void howTheEnumerationCrossesReadsTheAnswerAndNoCaseBesideIt() {
        Compilation c = compiled(SOURCE);
        Shapes.TypeAlternatives crossing =
                new Shapes.TypeAlternatives(MODULE, Type.ref(named("Stage")));
        assertInstanceOf(Boundary.Representation.Enumeration.class,
                c.db().ask(crossing).value().representation(), "Stage crosses as a bare tag");

        Set<Key<?>> read = c.db().dependenciesOf(crossing);
        assertTrue(read.contains(new Shapes.SumCasesOf(named("Stage"))),
                () -> "how Stage crosses was decided without the answer for it: " + read);
        for (String unnamed : List.of("Prospecting", "Qualified", "Won")) {
            assertTrue(read.stream().noneMatch(new Names.DeclarationKindOf(key(unnamed))::equals),
                    () -> "how Stage crosses read what " + unnamed + " is beside the answer: "
                            + read);
        }
    }

    /**
     * Nor what the enumeration itself says. That is what the answer for it is made out of, and a
     * reader reading it is a reader that could take the cases from there.
     */
    @Test
    void aReaderOrderingAValueOfTheEnumerationDoesNotReadWhatTheEnumerationSays() {
        Compilation c = compiled(SOURCE);

        for (Key<?> reader : READERS) {
            Set<Key<?>> read = c.db().dependenciesOf(reader);
            assertTrue(read.stream().noneMatch(new Shapes.MeaningOf(key("Stage"))::equals),
                    () -> reader + " read what Stage says beside the answer for it: " + read);
        }
    }

    /**
     * Which enumerations list a value is read off the same answer: the module's listing depends on
     * what each of its sums can be, and does not work their cases out again.
     */
    @Test
    void whatListsAValueIsReadOffWhatEachSumCanBe() {
        Compilation c = compiled(SOURCE);

        Set<Key<?>> read = c.db().dependenciesOf(new Shapes.EnumerationsListingIn(MODULE));
        assertTrue(read.contains(new Shapes.SumCasesOf(named("Stage"))),
                () -> "the module's listing worked out Stage's cases itself: " + read);
        assertTrue(read.stream().noneMatch(new Shapes.MeaningOf(key("Stage"))::equals),
                () -> "the module's listing read what Stage says: " + read);
    }

    /** A declaration of another form is no sum, and the compilation answers nothing for it. */
    @Test
    void aDeclarationThatIsNoSumHasNoAnswer() {
        Compilation c = compiled(SOURCE);

        assertNull(Shapes.sumCases(c.db()).of(named("Won")));
        assertNull(Shapes.sumCases(c.db()).of(named("Deal")));
    }
}
