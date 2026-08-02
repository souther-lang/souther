package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Located;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge): a construction whose
 * invariant the guards discharge is silent; one they leave possibly-violated is a warning (a possible
 * abort); one proven to violate on a reachable path is a compile error. Seeding an input's invariant
 * (a newtype's own bound, a product data's relation between fields) is what lets a guarded or reified
 * construction discharge.
 */
class CompileInvariantDischargeTest {

    private static long warnings(Compiler.Compiled c) {
        return c.warnings().stream().map(Located::diagnostic)
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    private static boolean hasWarning(Compiler.Compiled c, String code) {
        return c.warnings().stream().map(Located::diagnostic)
                .anyMatch(d -> d.severity() == Severity.WARNING && code.equals(d.code()));
    }

    @Test
    void aConstructionProvenToViolateIsAnError() {
        // 0 - 1 = -1, which the non-negative invariant rejects — proven at compile time
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                behavior calc : (m: Money) -> Money constructs Money
                let calc (m) = Money(0m) - Money(1m)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(),
                "a definite violation is E2010: " + e.getMessage());
    }

    @Test
    void aSumOfNonNegativesDischarges() {
        // a, b >= 0 (their own invariant) => a + b >= 0, so the re-wrap needs no guard — no warning
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior total : (p: Pair) -> Money
                let total (p) = p.a + p.b
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)));
    }

    @Test
    void anUnguardedSubtractionIsAPossibleViolationWarning() {
        // a - b can go negative with no guard relating a and b — a possible abort, warned by default
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Pair = { a: Money, b: Money }
                behavior diff : (p: Pair) -> Money
                let diff (p) = p.a - p.b
                """;
        Compiler.Compiled c = Compiler.compileWithWarnings(m);
        assertFalse(c.classes().isEmpty(), "a warning does not fail the build");
        assertTrue(hasWarning(c, "E2011"), "an unguarded subtraction should warn (E2011)");
    }

    @Test
    void reifyingTheRelationAsAnInvariantDischarges() {
        // declaring `額 <= 残高` on the input data lets the subtraction discharge with no guard here
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data 引落指示 = { 残高: Money, 額: Money }
                    invariant 額 <= 残高
                behavior 差引く : (指示: 引落指示) -> Money
                let 差引く (指示) = 指示.残高 - 指示.額
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the reified relation discharges the subtraction");
    }

    @Test
    void emptinessAndItsSizeComparisonAreOneStatement() {
        // `Set.isEmpty(s)` and `Set.size(s) == 0` say one thing, so which the author reached for does
        // not decide whether the construction discharges
        String m = """
                module demo
                data Empty
                data Tags = Set<String>
                    invariant Bool.not(Set.isEmpty(value))
                behavior build : (s: Set<String>) -> Tags | Empty constructs Tags, Empty
                let build (s) = {
                    guard Set.size(s) >= 1
                        else Empty
                    Tags(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the size guard discharges the emptiness invariant");
    }

    @Test
    void aListSaysItsEmptinessTwoWaysAndBothDischarge() {
        String m = """
                module demo
                data Empty
                data Items = List<String>
                    invariant Bool.not(List.isEmpty(value))
                behavior build : (xs: List<String>) -> Items | Empty constructs Items, Empty
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else Empty
                    Items(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the length guard discharges the emptiness invariant");
    }

    @Test
    void aMapSaysItsEmptinessTwoWaysAndBothDischarge() {
        String m = """
                module demo
                data Empty
                data Rates = Map<String, Int>
                    invariant Bool.not(Map.isEmpty(value))
                behavior build : (m: Map<String, Int>) -> Rates | Empty constructs Rates, Empty
                let build (m) = {
                    guard Map.size(m) >= 1
                        else Empty
                    Rates(m)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the size guard discharges the emptiness invariant");
    }

    @Test
    void aStringSaysItsEmptinessTwoWaysAndBothDischarge() {
        String m = """
                module demo
                data Empty
                data Code = String
                    invariant Bool.not(String.isEmpty(value))
                behavior build : (s: String) -> Code | Empty constructs Code, Empty
                let build (s) = {
                    guard String.length(s) >= 1
                        else Empty
                    Code(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the length guard discharges the emptiness invariant");
    }

    @Test
    void theElementAMapHandsItsClosureCarriesItsOwnInvariant() {
        // The combinator rule for `List.map` binds the closure's parameter to the list's element type
        // and seeds that type's invariant, so `x >= 0` is known here and the re-wrap discharges. This
        // only happens if the analysis reads a representation where `List.map` is still `List.map`:
        // against the tree the backend emits it is a fold, and the rule has nothing to match.
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Positive = Decimal
                    invariant value >= 0m
                data Bag = { items: List<Money> }
                behavior copy : (b: Bag) -> List<Positive> constructs Positive
                let copy (b) = List.map(x -> Positive(x.value), b.items)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the element's own invariant discharges the re-wrap");
    }

    @Test
    void aConstructionInsideAMapClosureIsAnalyzed() {
        // the closure element x: Money carries x >= 0; `x - Money(1m)` can go negative, so it is a
        // possible violation. Without binding the combinator's element parameter the construction
        // would be opaque (no diagnostic) — this pins that the closure body is analyzed.
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data Bag = { items: List<Money> }
                behavior shift : (b: Bag) -> List<Money> constructs Money
                let shift (b) = List.map(x -> x - Money(1m), b.items)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a construction inside a map closure should be analyzed");
    }

    @Test
    void anUnguardedListLengthConstructionIsAPossibleViolationWarning() {
        // `List.length(xs)` is a term the domain can name, so an invariant over it is expressible and
        // the unguarded construction is flagged rather than left silent
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(xs)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded length invariant should warn (E2011)");
    }

    @Test
    void aGuardOnTheLengthDischargesTheConstruction() {
        // the guard and the invariant name the same list, so they name the same atom
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    Lines(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the length invariant");
    }

    @Test
    void aGuardOnAnotherListDoesNotDischarge() {
        // the atom is keyed by the container the call names — guarding `ys` says nothing about `xs`
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>, ys: List<Int>) -> Lines | NoItems
                    constructs Lines, NoItems
                let build (xs, ys) = {
                    guard List.length(ys) >= 1
                        else NoItems
                    Lines(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a guard on another list should not discharge");
    }

    @Test
    void aGuardOnAStringLengthDischargesTheConstruction() {
        String m = """
                module demo
                data TooShort
                data Name = String
                    invariant String.length(value) >= 3
                behavior build : (s: String) -> Name | TooShort constructs Name, TooShort
                let build (s) = {
                    guard String.length(s) >= 3
                        else TooShort
                    Name(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the string-length invariant");
    }

    @Test
    void anUnguardedStringLengthConstructionIsAPossibleViolationWarning() {
        String m = """
                module demo
                data Name = String
                    invariant String.length(value) >= 3
                behavior build : (s: String) -> Name constructs Name
                let build (s) = Name(s)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded string-length invariant should warn (E2011)");
    }

    @Test
    void aGuardOnASetSizeDischargesTheConstruction() {
        String m = """
                module demo
                data Empty
                data Tags = Set<String>
                    invariant Set.size(value) >= 1
                behavior build : (s: Set<String>) -> Tags | Empty constructs Tags, Empty
                let build (s) = {
                    guard Set.size(s) >= 1
                        else Empty
                    Tags(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the set-size invariant");
    }

    @Test
    void aGuardOnAMapSizeDischargesTheConstruction() {
        String m = """
                module demo
                data Empty
                data Index = Map<String, Int>
                    invariant Map.size(value) >= 1
                behavior build : (m: Map<String, Int>) -> Index | Empty constructs Index, Empty
                let build (m) = {
                    guard Map.size(m) >= 1
                        else Empty
                    Index(m)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the map-size invariant");
    }

    @Test
    void anInputTypesLengthInvariantIsSeeded() {
        // `l: Lines` was built through Lines' checked construction, so its length is known here
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                data Batch = List<Int>
                    invariant List.length(value) >= 1
                behavior rewrap : (l: Lines) -> Batch constructs Batch
                let rewrap (l) = Batch(l.value)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the input newtype's length invariant discharges the re-wrap");
    }

    @Test
    void anUnguardedConstructionFromAMappedListIsReported() {
        // the length of the mapped list is the length of `xs`, and nothing here says what that is
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(List.map(x -> x + 1, xs))
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the length of the mapped list is the length of what was mapped");
    }

    @Test
    void aGuardRestatingASumOfTwoLengthsDischarges() {
        // the guard is the invariant written over the arguments. A sum of two atoms is outside the
        // interval/difference shapes, so what discharges it is the form itself being assumed.
        String m = """
                module demo
                data Empty
                data Matches = { accounts: List<Int>, contacts: List<Int> }
                    invariant List.length(accounts) + List.length(contacts) >= 1
                behavior build : (xs: List<Int>, ys: List<Int>) -> Matches | Empty
                    constructs Matches, Empty
                let build (xs, ys) = {
                    guard List.length(xs) + List.length(ys) >= 1
                        else Empty
                    Matches { accounts = xs, contacts = ys }
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a guard restating the invariant discharges it");
    }

    @Test
    void aGuardWeakerThanTheInvariantDoesNotDischarge() {
        String m = """
                module demo
                data Empty
                data Matches = { accounts: List<Int>, contacts: List<Int> }
                    invariant List.length(accounts) + List.length(contacts) >= 2
                behavior build : (xs: List<Int>, ys: List<Int>) -> Matches | Empty
                    constructs Matches, Empty
                let build (xs, ys) = {
                    guard List.length(xs) + List.length(ys) >= 1
                        else Empty
                    Matches { accounts = xs, contacts = ys }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a guard that establishes less should not discharge");
    }

    @Test
    void aNewtypeFieldsValueIsTheSameLocationOnBothSides() {
        // `n` was built through `Name`'s checked construction, so its length is known here — and the
        // clause names the very location the input's own invariant is about
        String m = """
                module demo
                data Name = String
                    invariant String.length(value) >= 3
                data Person = { name: Name }
                    invariant String.length(name.value) >= 3
                behavior build : (n: Name) -> Person constructs Person
                let build (n) = Person { name = n }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a newtype's `.value` is one location whichever side names it");
    }

    @Test
    void aGuardOnANewtypeFieldsValueDischarges() {
        String m = """
                module demo
                data TooShort
                data Name = String
                data Person = { name: Name }
                    invariant String.length(name.value) >= 3
                behavior build : (n: Name) -> Person | TooShort constructs Person, TooShort
                let build (n) = {
                    guard String.length(n.value) >= 3
                        else TooShort
                    Person { name = n }
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard sizes the same location the clause does");
    }

    @Test
    void aGuardThroughTwoNewtypesDischarges() {
        // the guard writes both `.value`s and the clause writes both, and each is the same location
        String m = """
                module demo
                data TooShort
                data Inner = String
                data Outer = Inner
                data Box = { held: Outer }
                    invariant String.length(held.value.value) >= 3
                behavior build : (o: Outer) -> Box | TooShort constructs Box, TooShort
                let build (o) = {
                    guard String.length(o.value.value) >= 3
                        else TooShort
                    Box { held = o }
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "each `.value` of a single-value newtype is the same location");
    }

    @Test
    void aNewtypeOverANewtypeIsStillOneLocation() {
        String m = """
                module demo
                data Inner = String
                    invariant String.length(value) >= 3
                data Outer = Inner
                data Box = { held: Outer }
                    invariant String.length(held.value.value) >= 3
                behavior build : (o: Outer) -> Box constructs Box
                let build (o) = Box { held = o }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "each `.value` of a single-value newtype is the same location");
    }

    @Test
    void aGuardOnAnotherNewtypesValueDoesNotDischarge() {
        String m = """
                module demo
                data TooShort
                data Name = String
                data Person = { name: Name }
                    invariant String.length(name.value) >= 3
                behavior build : (n: Name, other: Name) -> Person | TooShort
                    constructs Person, TooShort
                let build (n, other) = {
                    guard String.length(other.value) >= 3
                        else TooShort
                    Person { name = n }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "collapsing `.value` does not collapse two different newtypes into one");
    }

    @Test
    void aRebindingOfTheGuardedNameDropsTheFact() {
        // `xs` is rebound between the guard and the construction, so the guard's fact no longer holds
        // of what `Lines` is built from
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    let xs = List.filter(x -> x > 0, xs)
                    Lines(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a rebinding invalidates the guard's fact about that name");
    }

    @Test
    void aGuardOnAUniquenessPredicateDischargesTheConstruction() {
        // the guard and the clause project the same way over the same list, so they are one fact
        String m = """
                module demo
                data Duplicate
                data Lines = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Lines | Duplicate constructs Lines, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(x -> x, xs)
                        else Duplicate
                    Lines(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the uniqueness invariant");
    }

    @Test
    void anUnguardedUniquenessConstructionIsAPossibleViolationWarning() {
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(xs)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "an unguarded uniqueness invariant should warn (E2011)");
    }

    @Test
    void aGuardWritingAnotherProjectionDoesNotDischarge() {
        // uniqueness by `.a` says nothing about uniqueness by `.b`
        String m = """
                module demo
                data Duplicate
                data Row = { a: Int, b: Int }
                data Rows = List<Row>
                    invariant List.allUniqueBy(r -> r.b, value)
                behavior build : (xs: List<Row>) -> Rows | Duplicate constructs Rows, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(r -> r.a, xs)
                        else Duplicate
                    Rows(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a guard on another projection should not discharge");
    }

    @Test
    void aClosureIsTheSameTermWhateverItsParameterIsCalled() {
        // the parameter's spelling is not part of what the closure computes
        String m = """
                module demo
                data Duplicate
                data Row = { a: Int, b: Int }
                data Rows = List<Row>
                    invariant List.allUniqueBy(r -> r.a, value)
                behavior build : (xs: List<Row>) -> Rows | Duplicate constructs Rows, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(row -> row.a, xs)
                        else Duplicate
                    Rows(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "renaming the closure parameter does not change the term");
    }

    @Test
    void theProjectionShorthandIsTheSameTermAsTheClosure() {
        String m = """
                module demo
                data Duplicate
                data Row = { a: Int, b: Int }
                data Rows = List<Row>
                    invariant List.allUniqueBy(.a, value)
                behavior build : (xs: List<Row>) -> Rows | Duplicate constructs Rows, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(r -> r.a, xs)
                        else Duplicate
                    Rows(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "`.a` and `r -> r.a` are one term");
    }

    @Test
    void aGuardOnMembershipDischargesTheConstruction() {
        String m = """
                module demo
                data Unknown
                data Known = String
                    invariant List.member(value, ["a", "b"])
                behavior build : (s: String) -> Known | Unknown constructs Known, Unknown
                let build (s) = {
                    guard List.member(s, ["a", "b"])
                        else Unknown
                    Known(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the membership guard discharges the construction");
    }

    @Test
    void aLiteralHoldingTheKeysOwnPunctuationIsAnotherTerm() {
        // one element whose value is `a", "b` is not the two elements `a` and `b`
        String m = """
                module demo
                data Unknown
                data Known = String
                    invariant List.member(value, ["a\\", \\"b"])
                behavior build : (s: String) -> Known | Unknown constructs Known, Unknown
                let build (s) = {
                    guard List.member(s, ["a", "b"])
                        else Unknown
                    Known(s)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "another list is another fact however its elements are spelled");
    }

    @Test
    void aNewlineAndTheTwoCharactersSpellingItAreDifferentTerms() {
        String m = """
                module demo
                data Unknown
                data Known = String
                    invariant List.member(value, ["a\\nb"])
                behavior build : (s: String) -> Known | Unknown constructs Known, Unknown
                let build (s) = {
                    guard List.member(s, ["a\\\\nb"])
                        else Unknown
                    Known(s)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a newline is not the backslash and the n that spell it");
    }

    @Test
    void aGuardOnAPatternMatchDischargesTheConstruction() {
        String m = """
                module demo
                data Malformed
                data Code = String
                    invariant String.matches("[A-Z]{2}-[0-9]{4}", value)
                behavior build : (s: String) -> Code | Malformed constructs Code, Malformed
                let build (s) = {
                    guard String.matches("[A-Z]{2}-[0-9]{4}", s)
                        else Malformed
                    Code(s)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the pattern guard discharges the construction");
    }

    @Test
    void aDifferentPatternDoesNotDischarge() {
        String m = """
                module demo
                data Malformed
                data Code = String
                    invariant String.matches("[A-Z]{2}-[0-9]{4}", value)
                behavior build : (s: String) -> Code | Malformed constructs Code, Malformed
                let build (s) = {
                    guard String.matches("[A-Z]{3}-[0-9]{4}", s)
                        else Malformed
                    Code(s)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "another pattern is another fact");
    }

    @Test
    void aPredicateTheGuardsSettleFalseIsADefiniteViolation() {
        // on the else branch the predicate is known not to hold, so the construction must abort
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) =
                    if List.allUniqueBy(x -> x, xs) then Lines(xs) else Lines(xs)
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(),
                "a predicate settled false is a definite violation: " + e.getMessage());
    }

    @Test
    void aNegatedGuardSettlesThePredicateOnTheMainline() {
        // `Bool.not(p)` on the guard leaves `p` false where the construction stands
        String m = """
                module demo
                data Ok
                data Lines = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Lines | Ok constructs Lines, Ok
                let build (xs) = {
                    guard Bool.not(List.allUniqueBy(x -> x, xs))
                        else Ok
                    Lines(xs)
                }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(m));
        assertEquals("E2010", e.diagnostic().code(),
                "the negated guard settles the predicate false: " + e.getMessage());
    }

    @Test
    void anInputTypesPredicateInvariantIsSeeded() {
        String m = """
                module demo
                data Row = { a: Int }
                data Rows = List<Row>
                    invariant List.allUniqueBy(r -> r.a, value)
                data Batch = List<Row>
                    invariant List.allUniqueBy(r -> r.a, value)
                behavior rewrap : (rs: Rows) -> Batch constructs Batch
                let rewrap (rs) = Batch(rs.value)
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the input newtype's uniqueness invariant discharges the re-wrap");
    }

    @Test
    void aFreeNameInsideTheClosureIsPartOfTheTerm() {
        // the clause's `floor` is the field being given, so the guard has to bound by the same value
        String m = """
                module demo
                data TooSmall
                data Bounded = { items: List<Int>, floor: Int }
                    invariant List.all(x -> x >= floor, items)
                behavior build : (xs: List<Int>, lo: Int, hi: Int) -> Bounded | TooSmall
                    constructs Bounded, TooSmall
                let build (xs, lo, hi) = {
                    guard List.all(x -> x >= hi, xs)
                        else TooSmall
                    Bounded { items = xs, floor = lo }
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a guard bounding by another value should not discharge");
    }

    @Test
    void aRebindingDropsThePredicateFact() {
        String m = """
                module demo
                data Duplicate
                data Lines = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Lines | Duplicate constructs Lines, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(x -> x, xs)
                        else Duplicate
                    let xs = xs ++ [1]
                    Lines(xs)
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a rebinding invalidates the guard's fact about that name");
    }

    @Test
    void aMappingKeepsTheLengthOfWhatItMapped() {
        // the crm case: guard the input's length, build from the mapped list. How the elements are
        // made has no bearing on how many there are.
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    Lines(List.map(x -> x + 1, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a mapping keeps the length");
    }

    @Test
    void aReorderingKeepsTheLength() {
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    Lines(List.reverse(List.sort(xs)))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "reversing and sorting keep the length");
    }

    @Test
    void aSelectionOnlyBoundsTheLength() {
        // filtering can drop everything, so guarding the input says nothing about the result
        String m = """
                module demo
                data NoItems
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                behavior build : (xs: List<Int>) -> Lines | NoItems constructs Lines, NoItems
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoItems
                    Lines(List.filter(x -> x > 0, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a selection does not keep the length");
    }

    @Test
    void aSelectionBoundsTheLengthFromAbove() {
        // the other direction is known: no more came out than went in, so a cap on the input caps
        // the result
        String m = """
                module demo
                data TooMany
                data Lines = List<Int>
                    invariant List.length(value) <= 10
                behavior build : (xs: List<Int>) -> Lines | TooMany constructs Lines, TooMany
                let build (xs) = {
                    guard List.length(xs) <= 10
                        else TooMany
                    Lines(List.filter(x -> x > 0, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "no more came out of the filter than went in");
    }

    @Test
    void aReorderingCarriesUniqueness() {
        String m = """
                module demo
                data Duplicate
                data Row = { a: Int }
                data Rows = List<Row>
                    invariant List.allUniqueBy(r -> r.a, value)
                behavior build : (xs: List<Row>) -> Rows | Duplicate constructs Rows, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(r -> r.a, xs)
                        else Duplicate
                    Rows(List.sortBy(r -> r.a, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "sorting keeps the elements, so it keeps their distinctness");
    }

    @Test
    void aSelectionCarriesAPropertyOfEveryElement() {
        String m = """
                module demo
                data OutOfRange
                data Row = { a: Int }
                data Rows = List<Row>
                    invariant List.all(r -> r.a >= 1, value)
                behavior build : (xs: List<Row>) -> Rows | OutOfRange constructs Rows, OutOfRange
                let build (xs) = {
                    guard List.all(r -> r.a >= 1, xs)
                        else OutOfRange
                    Rows(List.filter(r -> r.a > 5, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "nothing new is in a sublist, so what held of every element still holds");
    }

    @Test
    void aSelectionDoesNotCarryMembership() {
        String m = """
                module demo
                data Missing
                data Rows = List<Int>
                    invariant List.member(1, value)
                behavior build : (xs: List<Int>) -> Rows | Missing constructs Rows, Missing
                let build (xs) = {
                    guard List.member(1, xs)
                        else Missing
                    Rows(List.filter(x -> x > 5, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a filter may drop the very element that was there");
    }

    @Test
    void aMappingDoesNotCarryUniqueness() {
        // distinct elements can map to one — that a projection survives a map is #226's question
        String m = """
                module demo
                data Duplicate
                data Rows = List<Int>
                    invariant List.allUniqueBy(x -> x, value)
                behavior build : (xs: List<Int>) -> Rows | Duplicate constructs Rows, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(x -> x, xs)
                        else Duplicate
                    Rows(List.map(x -> x * 0, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a mapping says nothing about what the elements became");
    }

    @Test
    void aProjectionTheClosureCopiesCarriesThroughTheMap() {
        // the crm case: guard uniqueness of the input by `.product`, build from the mapped list. The
        // closure copies `product` across, so two mapped rows differ there exactly when the two they
        // came from did.
        String m = """
                module demo
                data Duplicate
                data Row = { product: String, note: String }
                data Line = { product: String, label: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.product, value)
                let toLine (r: Row): Line = Line { product = r.product, label = r.note }
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.product, xs)
                        else Duplicate
                    Lines(List.map(r -> toLine(r), xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "a copied field carries uniqueness through the map");
    }

    @Test
    void aClosureBindingOverItsOwnParameterStillCopiesTheField() {
        // `let r = r` is the identity, so the field is still copied from the element
        String m = """
                module demo
                data Duplicate
                data Row = { sku: String }
                data Line = { code: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.code, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.sku, xs)
                        else Duplicate
                    Lines(List.map(r -> {
                        let r = r
                        Line { code = r.sku }
                    }, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "binding a name to itself is the identity, not a name standing for itself");
    }

    @Test
    void aFieldReadBeforeTheNameWasReboundIsNotTheElements() {
        // `a` reads the argument, and the later binding of that name does not reach back into it, so
        // nothing says the built field came from the element
        String m = """
                module demo
                data Duplicate
                data Row = { sku: String }
                data Line = { code: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.code, value)
                behavior build : (xs: List<Row>, spare: Row) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs, spare) = {
                    guard List.allUniqueBy(.sku, xs)
                        else Duplicate
                    Lines(List.map(r -> {
                        let a = spare
                        let spare = r
                        Line { code = a.sku }
                    }, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the field was copied from the argument, not from the element");
    }

    @Test
    void aProjectionCarriesToTheFieldItWasCopiedFrom() {
        // the closure renames the field, so uniqueness of the result by `.code` is uniqueness of the
        // input by `.sku`
        String m = """
                module demo
                data Duplicate
                data Row = { sku: String }
                data Line = { code: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.code, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.sku, xs)
                        else Duplicate
                    Lines(List.map(r -> Line { code = r.sku }, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the projection carries to the field it was copied from");
    }

    @Test
    void guardingTheWrongFieldDoesNotCarry() {
        String m = """
                module demo
                data Duplicate
                data Row = { sku: String, name: String }
                data Line = { code: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.code, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.name, xs)
                        else Duplicate
                    Lines(List.map(r -> Line { code = r.sku }, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "uniqueness by one field says nothing about another");
    }

    @Test
    void aComputedFieldDoesNotCarryAProjection() {
        // `code` is built rather than copied, so two rows that differ can still land on one code
        String m = """
                module demo
                data Duplicate
                data Row = { sku: String, name: String }
                data Line = { code: String }
                data Lines = List<Line>
                    invariant List.allUniqueBy(.code, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.sku, xs)
                        else Duplicate
                    Lines(List.map(r -> Line { code = String.concat([r.sku, r.name]) }, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "a computed field is not a copied one");
    }

    @Test
    void bothClausesOfAMappedConstructionDischargeTogether() {
        // #222's target shape: a length clause and a uniqueness clause over the same mapped list,
        // each discharged by its own guard
        String m = """
                module demo
                data Duplicate
                data NoLines
                data Row = { product: String }
                data Line = { product: String }
                data Lines = List<Line>
                    invariant List.length(value) >= 1 && List.allUniqueBy(.product, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate | NoLines
                    constructs Lines, Line, Duplicate, NoLines
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else NoLines
                    guard List.allUniqueBy(.product, xs)
                        else Duplicate
                    Lines(List.map(r -> Line { product = r.product }, xs))
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "both clauses discharge");
    }

    @Test
    void removingOneOfTheTwoGuardsIsReported() {
        String m = """
                module demo
                data Duplicate
                data Row = { product: String }
                data Line = { product: String }
                data Lines = List<Line>
                    invariant List.length(value) >= 1 && List.allUniqueBy(.product, value)
                behavior build : (xs: List<Row>) -> Lines | Duplicate
                    constructs Lines, Line, Duplicate
                let build (xs) = {
                    guard List.allUniqueBy(.product, xs)
                        else Duplicate
                    Lines(List.map(r -> Line { product = r.product }, xs))
                }
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the length clause is no longer established");
    }

    @Test
    void aRequireGuardDischargesTheSubtraction() {
        // `guard 額 <= 残高` establishes the relation on the mainline, discharging `残高 - 額`
        String m = """
                module demo
                data Money = Decimal
                    invariant value >= 0m
                data 残高不足
                data 引落指示 = { 残高: Money, 額: Money }
                behavior 差引く : (指示: 引落指示) -> Money | 残高不足
                let 差引く (指示) = {
                    guard 指示.額 <= 指示.残高
                        else 残高不足
                    指示.残高 - 指示.額
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the guard discharges the subtraction");
    }

    @Test
    void guardsThatCannotAllHoldLeaveNothingToReport() {
        // `a <= b`, `b <= 0` and `a >= 1` cannot hold together, so the construction is not reached and
        // says nothing about the invariant — the bound on `a` is only derivable through the difference
        String m = """
                module demo
                data Ok
                data AtLeastTwo = Int
                    invariant value >= 2
                behavior build : (a: Int, b: Int) -> AtLeastTwo | Ok constructs AtLeastTwo, Ok
                let build (a, b) = {
                    guard a <= b
                        else Ok
                    guard b <= 0
                        else Ok
                    guard a >= 1
                        else Ok
                    AtLeastTwo(a)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "an unreachable construction is neither violated nor possibly violated");
    }

    @Test
    void theOrderTheContradictingGuardsAreWrittenDoesNotMatter() {
        String m = """
                module demo
                data Ok
                data AtLeastTwo = Int
                    invariant value >= 2
                behavior build : (a: Int, b: Int) -> AtLeastTwo | Ok constructs AtLeastTwo, Ok
                let build (a, b) = {
                    guard a >= 1
                        else Ok
                    guard b <= 0
                        else Ok
                    guard a <= b
                        else Ok
                    AtLeastTwo(a)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "the difference asserted last closes the same contradiction");
    }

    @Test
    void aComparisonAndItsDenialAreOneFact() {
        // the else branch of `a == b` is where `a /= b` holds
        String m = """
                module demo
                data Ok
                data Pair = { left: Int, right: Int }
                    invariant left /= right
                behavior build : (a: Int, b: Int) -> Pair | Ok constructs Pair, Ok
                let build (a, b) =
                    if a == b then Ok else Pair { left = a, right = b }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "denying the equality states the inequality");
    }

    @Test
    void anEqualityIsOneFactWhicheverSideIsWrittenFirst() {
        String m = """
                module demo
                data Ok
                data Pair = { left: Int, right: Int }
                    invariant right /= left
                behavior build : (a: Int, b: Int) -> Pair | Ok constructs Pair, Ok
                let build (a, b) =
                    if a == b then Ok else Pair { left = a, right = b }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "which side of an equality a term is written on is not part of what it says");
    }

    @Test
    void aClauseTheCheckCannotReadLeavesTheOthersReported() {
        // the second clause is a shape the check does not read (a comprehension), and the first is a
        // length it derives over — writing them together does not cost the first its guard
        String m = """
                module demo
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                           && List.length([1 | List.length(value) >= 1]) >= 1
                behavior build : (xs: List<Int>) -> Lines constructs Lines
                let build (xs) = Lines(xs)
                """;
        assertTrue(hasWarning(Compiler.compileWithWarnings(m), "E2011"),
                "the derivable clause is still unproven, and guarding it is still open to the author");
    }

    @Test
    void aClauseTheCheckCannotReadIsNotItselfReported() {
        String m = """
                module demo
                data Ok
                data Lines = List<Int>
                    invariant List.length(value) >= 1
                           && List.length([1 | List.length(value) >= 1]) >= 1
                behavior build : (xs: List<Int>) -> Lines | Ok constructs Lines, Ok
                let build (xs) = {
                    guard List.length(xs) >= 1
                        else Ok
                    Lines(xs)
                }
                """;
        assertEquals(0, warnings(Compiler.compileWithWarnings(m)),
                "what is reported is a clause a guard could discharge, and the comprehension is not one");
    }
}
