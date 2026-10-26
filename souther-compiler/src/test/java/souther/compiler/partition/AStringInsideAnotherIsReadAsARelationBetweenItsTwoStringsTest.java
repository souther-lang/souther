package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.semantics.StringContainment;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One string standing inside another is read as a relation between the two strings, whatever the
 * strings are made of.
 *
 * <p>A statement over two strings is no language one of them is in: {@code String.contains(a, b)}
 * is true of {@code b} for the {@code a} inside it, and of {@code a} for the {@code b} it holds,
 * and says nothing of either alone. So it is held as the two strings and where one stands in the
 * other, each string as the value of the input it is or as what an operation answers of one — a
 * lowercased string keeps what it was lowercased from.
 */
class AStringInsideAnotherIsReadAsARelationBetweenItsTwoStringsTest {

    private static final String DECLARATIONS = """
            module demo

            data In = { a: String, b: String, c: String, bs: List<String> }

            let lowered (s: String): String = String.lowercase(s)
            """;

    private static DecisionAtom.OfTheInput value(String field) {
        return new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(TermPath.of("i").then(field)));
    }

    private static Quantity lowercased(String field) {
        return new Quantity.WhatAnOperationAnswers(
                ValueName.Stdlib.operation("String", "lowercase"), List.of(value(field)));
    }

    private static Proposition stated(String condition) {
        Compilation compilation = Compilation.ofSource(DECLARATIONS + """

                behavior f : (i: In) -> Int
                let f (i) =
                    if (%s) then 1 else 0
                """.formatted(condition), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), () -> "compiles: " + condition);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("demo")).value();
        AnalysisBody analysis = checked.analysisBodies().get("f");
        RuleReadingSource rules = RuleReadings.of(compilation, "demo");
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs("demo")).value().get("f");
        InputReading read = inputs.reading(rules);
        InputReads reads = InputReads.ofParametersWhereCallsStand(inputs.parameterReads(),
                inputs.declared(rules), ElementBindings.of(analysis, rules.newtypes()),
                inputs.dependencies());
        Core.If fork = assertInstanceOf(Core.If.class, Core.withoutStanding(analysis.core()));
        return Pullback.ofATruth(fork.cond(), reads, read, Optional.empty()).proposition();
    }

    /** The string looked for is the first argument and the string looked in the second. */
    @Test
    void twoStringsOfTheInputAreTheTwoStringsRelated() {
        assertEquals(new Proposition.StringInside(value("a"), value("b"),
                StringContainment.ANYWHERE, true), stated("String.contains(i.a, i.b)"));
    }

    /** Where the string stands in the other is the only difference between the three. */
    @Test
    void whereTheStringStandsIsWhatTellsTheThreeApart() {
        assertEquals(new Proposition.StringInside(value("a"), value("b"),
                StringContainment.AT_THE_START, true), stated("String.startsWith(i.a, i.b)"));
        assertEquals(new Proposition.StringInside(value("a"), value("b"),
                StringContainment.AT_THE_END, true), stated("String.endsWith(i.a, i.b)"));
        assertEquals(new Proposition.StringInside(value("a"), value("b"),
                StringContainment.ANYWHERE, true), stated("String.contains(i.a, i.b)"));
    }

    /** Not inside is the same relation turned over, and no other: turned into a relation of its
     *  own, a denial inside a quantifier would forget what it denies. */
    @Test
    void notInsideIsTheSameRelationDenied() {
        Proposition inside = stated("String.contains(i.a, i.b)");
        assertEquals(inside.denied(), stated("Bool.not(String.contains(i.a, i.b))"));
        assertEquals(inside, inside.denied().denied());
    }

    /** A string made of another keeps what it was made of, on either side. */
    @Test
    void aLowercasedStringIsWhatItWasLowercasedFrom() {
        assertEquals(new Proposition.StringInside(lowercased("a"), lowercased("b"),
                StringContainment.ANYWHERE, true),
                stated("String.contains(String.lowercase(i.a), String.lowercase(i.b))"));
        assertEquals(new Proposition.StringInside(lowercased("a"), value("b"),
                StringContainment.ANYWHERE, true),
                stated("String.contains(String.lowercase(i.a), i.b)"));
    }

    /** Made through a helper of the module, a string is made of what the helper was handed. */
    @Test
    void aStringMadeThroughAHelperIsWhatTheHelperWasHanded() {
        assertEquals(new Proposition.StringInside(lowercased("a"), lowercased("b"),
                StringContainment.ANYWHERE, true),
                stated("String.contains(lowered(i.a), lowered(i.b))"));
    }

    /** The string looked in is each element of a list when the list is asked, and the relation
     *  is the one some element has. */
    @Test
    void aStringInsideSomeElementIsTheRelationOfThatElement() {
        TermPath element = TermPath.of("i").then("bs").element();
        Proposition some = stated("List.any(s -> String.contains(i.a, s), i.bs)");
        Proposition.Some quantified = assertInstanceOf(Proposition.Some.class, some);
        assertEquals(new Proposition.StringInside(value("a"),
                new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(element)),
                StringContainment.ANYWHERE, true), quantified.ofTheElement());
    }

    /** Two spellings of one relation are one statement, and two different relations are not. */
    @Test
    void theRelationIsToldApartByTheStringsAndWhereOneStandsInTheOther() {
        assertEquals(stated("String.contains(i.a, i.b)").key(),
                stated("String.contains(i.a, i.b)").key());
        assertTrue(!stated("String.contains(i.a, i.b)").key()
                .equals(stated("String.contains(i.b, i.a)").key()), "the strings swapped");
        assertTrue(!stated("String.contains(i.a, i.b)").key()
                .equals(stated("String.startsWith(i.a, i.b)").key()), "where one stands");
        assertTrue(!stated("String.contains(i.a, i.b)").key()
                .equals(stated("String.contains(String.lowercase(i.a), i.b)").key()),
                "what one was made of");
    }

    /** A string this does not know to be a value of the input or an answer made of one is no
     *  relation of the input's strings, and is not read as one. */
    @Test
    void aStringMadeOfSomethingElseIsNotReadAsARelation() {
        Proposition appended = stated("String.contains(i.a, String.append(i.b, \"x\"))");
        assertTrue(!(appended instanceof Proposition.StringInside),
                () -> "a string with a constant in it is no value of the input: " + appended);
    }
}
