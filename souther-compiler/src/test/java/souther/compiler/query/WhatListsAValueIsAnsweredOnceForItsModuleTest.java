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
import java.util.stream.Collectors;

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
                Shapes.declarationKinds(c.db()), Shapes.sumCases(c.db()));
        EnumerationListings held = Shapes.enumerationListings(c.db());

        for (String unit : List.of("Prospecting", "Qualified", "Won", "Lost", "Alone", "Ok")) {
            assertEquals(walked.of(value(unit)), held.of(value(unit)), unit);
        }
        assertEquals(Set.of(value("Stage"), value("Closing")), held.of(value("Won")),
                "a case of two enumerations is listed by both");
        assertEquals(Set.of(), held.of(value("Alone")), "and a unit of none by none");
    }

    /**
     * A case of an enumeration the language declares is listed by it like any other. No module of
     * the compilation writes the library's declarations, so a module's names read off what its
     * sources declare would have none here, and every case of it would be ordered by nothing.
     */
    @Test
    void aCaseTheLanguageDeclaresIsListedByItsEnumeration() {
        Compilation c = compiled();

        assertEquals(Set.of(TypeSymbols.declared(new TypeKey("souther.decimal", "RoundingMode"))),
                Shapes.enumerationListings(c.db()).of(
                        TypeSymbols.declared(new TypeKey("souther.decimal", "HALF_UP"))));
    }

    /** And two of its cases compare, which is the order a reader of one relies on. */
    @Test
    void twoCasesTheLanguageDeclaresCompare() {
        Compilation c = Compilation.ofDocuments(Map.of("modes.sou", """
                module modes

                data Ok
                data No
                data Verdict = Ok | No

                behavior gentler : (x: Int) -> Verdict
                let gentler (x) = if HALF_UP < DOWN then Ok else No
                """), Set.of(), ModulePath.EMPTY);
        c.answerEverything();

        assertEquals(List.of(), c.db().allReports().stream()
                        .map(each -> each.report().diagnostic().code()).toList(),
                "two cases of the library's rounding modes are ordered by it");
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
     * And it finds the operands among the enumeration's cases through that answer too. Whether
     * {@code Won} is a case of what orders {@code Qualified} is what lists {@code Won}; opening the
     * enumeration to look reads what every case of it says, on every comparison.
     */
    @Test
    void aCheckedComparisonOpensNoCaseItDoesNotName() {
        Compilation c = compiled();
        Set<Key<?>> read = c.db().dependenciesOf(new Bodies.CheckedBehavior(MODULE, "advance"));

        assertTrue(read.stream().noneMatch(new Shapes.MeaningOf(key("Prospecting"))::equals),
                () -> "the comparison opened its enumeration to find the operands: " + read);
    }

    /**
     * And a helper's body is checked against the same answer. The module's check is handed the
     * compilation's answers to what is asked of a declaration, and a helper checked under it is
     * checked with those, not with a walk of the module made again out of its scope.
     */
    @Test
    void aCheckedHelperDependsOnTheAnswerForItsValue() {
        Compilation c = Compilation.ofDocuments(Map.of("shop.sou", SOURCE + """

                let early (s: Prospecting): Bool = s < Won

                behavior open : (s: Prospecting) -> Verdict
                let open (s) = if early(s) then Ok else No
                """), Set.of(), ModulePath.EMPTY);
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");
        Set<Key<?>> read = c.db().dependenciesOf(new Bodies.ModuleCheck(MODULE));

        assertTrue(read.contains(new Shapes.EnumerationsListing(key("Prospecting"))),
                () -> "the helper's comparison is ordered without the compilation's answer: "
                        + read);
    }

    /**
     * Two products whose invariants order a unit, and a sum that lists one of them beside a unit.
     * {@code Event} is no enumeration, and what lists a value is worked out by asking it.
     */
    private static final String PRODUCTS_ORDERING_A_UNIT = SOURCE + """

            data Deal =
                { at: Qualified
                }
                invariant early = at < Won

            data Lead =
                { at: Prospecting
                }
                invariant early = at < Won

            data Event = Deal | Prospecting
            """;

    /**
     * Making what a product says reads the answer for each value its invariant orders, the way a
     * checked body does, and for no other value. Its meaning is made with itself taken out of what
     * the declarations say, and that does not stop it from reading the compilation's answer: the
     * answer reads what the module's sums say, and a sum's meaning reads no clause.
     *
     * <p>Asked first, of a compilation that has answered nothing, so that nothing the answer reads
     * has already been answered by the time it is made. A walk for the answer that asked what a
     * case says before asking whether it is a sum would ask it of {@code Deal} through
     * {@code Event}, which is asking for the meaning being made.
     */
    @Test
    void whatAProductSaysDependsOnTheAnswerForEachValueItsInvariantOrders() {
        Compilation c = Compilation.ofDocuments(Map.of("shop.sou", PRODUCTS_ORDERING_A_UNIT),
                Set.of(), ModulePath.EMPTY);
        assertTrue(c.db().ask(new Shapes.MeaningOf(key("Deal"))).present(),
                "what `Deal` says is made before anything else is asked");
        c.answerEverything();
        assertTrue(c.db().allReports().isEmpty(), "the module compiles to begin with");

        Map<String, Set<Key<?>>> expected = Map.of(
                "Deal", Set.of(new Shapes.EnumerationsListing(key("Qualified")),
                        new Shapes.EnumerationsListing(key("Won"))),
                "Lead", Set.of(new Shapes.EnumerationsListing(key("Prospecting")),
                        new Shapes.EnumerationsListing(key("Won"))));
        expected.forEach((product, listings) -> {
            Set<Key<?>> read = c.db().dependenciesOf(new Shapes.MeaningOf(key(product)));
            assertEquals(listings, read.stream()
                            .filter(Shapes.EnumerationsListing.class::isInstance)
                            .collect(Collectors.toSet()),
                    () -> "what " + product + " says read the answers for other values: " + read);
            assertTrue(read.stream().noneMatch(Shapes.EnumerationsListingIn.class::isInstance),
                    () -> product + " read what lists every value of the module: " + read);
        });
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
