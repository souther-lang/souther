package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.EnumerationListings;
import souther.compiler.check.Symbols;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which enumerations list a unit value is the compilation's answer, worked out once for the
 * value's module, and a reader depends on the answer for the value it asks about.
 *
 * <p>The answer is read off every sum of the module, so a reader working it out for itself pays the
 * module for every value it orders. Held by the compilation, the module is walked once; held as one
 * answer per value, a sum of the module moving reaches only the readers whose value it lists.
 */
class WhatListsAValueIsAnsweredOnceForItsModuleTest {

    private static final String MODULE = "shop";

    /** {@code Won} is listed by two enumerations and {@code Alone} by none. */
    private static final String SOURCE = """
            module shop

            data Prospecting
            data Qualified
            data Won
            data Lost
            data Alone
            data Stage = Prospecting | Qualified | Won
            data Closing = Won | Lost

            data Ok
            data No
            data Verdict = Ok | No

            behavior advance : (s: Qualified) -> Verdict
            let advance (s) = if s < Won then Ok else No
            """;

    /** The same, with an enumeration beside the others that lists none of their cases. */
    private static final String WITH_ANOTHER_ENUMERATION = SOURCE + """

            data Red
            data Green
            data Colour = Red | Green
            """;

    private static Compilation compiled() {
        Compilation c = Compilation.ofDocuments(Map.of("shop.sou", SOURCE), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");
        return c;
    }

    private static TypeKey key(String name) {
        return new TypeKey(MODULE, name);
    }

    private static TypeSymbol.AtModule value(String name) {
        return TypeSymbols.declared(key(name));
    }

    /** What the compilation answers is what reading the declarations answers, value by value. */
    @Test
    void theCompilationAnswersAsTheDeclarationsDo() {
        Compilation c = compiled();
        Symbols symbols = Scopes.derived(c.db(), MODULE).value();
        EnumerationListings walked = EnumerationListings.asWritten(symbols,
                Shapes.declarationKinds(c.db()), Shapes.publishedDeclarations(c.db()));
        EnumerationListings held = Shapes.enumerationListings(c.db());

        for (String unit : List.of("Prospecting", "Qualified", "Won", "Lost", "Alone", "Ok")) {
            assertEquals(walked.of(value(unit)), held.of(value(unit)), unit);
        }
        assertEquals(Set.of(value("Stage"), value("Closing")), held.of(value("Won")),
                "a case of two enumerations is listed by both");
        assertEquals(Set.of(), held.of(value("Alone")), "and a unit of none by none");
    }

    /**
     * Checking a body that orders a unit reads the answer for that unit, and does not read the
     * module's whole answer or work it out again.
     */
    @Test
    void aCheckedBodyDependsOnTheAnswerForItsValue() {
        Compilation c = compiled();
        Set<Key<?>> read = c.db().dependenciesOf(new Bodies.CheckedBehavior(MODULE, "advance"));

        assertTrue(read.contains(new Shapes.EnumerationsListing(key("Qualified"))),
                () -> "the comparison is ordered without the compilation's answer: " + read);
        assertTrue(read.stream().noneMatch(Shapes.EnumerationsListingIn.class::isInstance),
                () -> "the comparison read what lists every value of the module: " + read);
    }

    /**
     * An enumeration added beside the others moves the module's answer and leaves the answer for a
     * value it does not list where it was — which is what keeps a reader of that value from being
     * asked again.
     */
    @Test
    void anEnumerationThatListsNoneOfAValueLeavesItsAnswerAlone() {
        Compilation c = compiled();
        Answer<Map<TypeKey, Set<TypeSymbol>>> moduleBefore =
                c.db().ask(new Shapes.EnumerationsListingIn(MODULE));
        Answer<Set<TypeSymbol>> before = c.db().ask(new Shapes.EnumerationsListing(key("Qualified")));

        c.update(Map.of("shop.sou", WITH_ANOTHER_ENUMERATION), Set.of());
        c.answerEverything();
        Answer<Map<TypeKey, Set<TypeSymbol>>> moduleAfter =
                c.db().ask(new Shapes.EnumerationsListingIn(MODULE));
        Answer<Set<TypeSymbol>> after = c.db().ask(new Shapes.EnumerationsListing(key("Qualified")));

        assertNotEquals(moduleBefore.value(), moduleAfter.value(),
                "the module lists two more values than it did");
        assertEquals(before.value(), after.value(),
                "and what lists `Qualified` is what it was");
    }
}
