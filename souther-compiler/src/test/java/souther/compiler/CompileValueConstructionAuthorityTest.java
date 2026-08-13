package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A threshold a rule is stated against is written once as a value, and a behavior that compares
 * against it originates nothing: the one construction on that path is the value's own, made where
 * the value is defined. Reading the name is not making the thing, so `constructs` stays what it is
 * for — telling a behavior that creates a value from one that passes an existing value through.
 *
 * <p>A value is substituted at each reference, and what the substitution brings in used to become
 * the reading behavior's own construction. It is marked as carried instead, the way a construction
 * that arrives in a published body already is. Carried is not absent: a behavior that declares the
 * authority anyway is still taken at its word, so this loosens nothing that was checked before.
 *
 * <p>What a helper builds stays the caller's, because a helper body is checked as though it had
 * been written inline.
 */
class CompileValueConstructionAuthorityTest {

    private static final String LIMIT = """
            module limit exposing ( Hours, floorHours )

            data Hours = Decimal invariant value >= 0.0m

            let floorHours = Hours(20.0m)
            """;

    @Test
    void aBehaviorComparingAgainstAValueNeedsNoAuthorityForTheValuesType() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorHours = Hours(20.0m)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** Publication is not what settles the question: the same value read in the module that
     * declares it is read the same way as one read from outside. */
    @Test
    void aValueThisModulePublishesIsReadInItTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m exposing ( Hours, TooShort, floorHours, judge )

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorHours = Hours(20.0m)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** The value is this module's and the type it builds is another module's. What the reading
     * behavior originates does not depend on where the type was declared. */
    @Test
    void aValueOfThisModuleMayBuildAnImportedType() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module limit exposing ( Hours )

                data Hours = Decimal invariant value >= 0.0m
                """, """
                module m

                import limit ( Hours )

                data TooShort

                let floorHours = Hours(20.0m)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """)));
    }

    /** Three modules: the type is declared in one, the value naming it in a second, and the value
     * that reads that one in a third. The reading behavior originates none of it. */
    @Test
    void aValueReachedThroughAnotherModulesValueCarriesTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(LIMIT, """
                module alias exposing ( floor )

                import limit ( Hours, floorHours )

                let floor = floorHours
                """, """
                module m

                import limit ( Hours )
                import alias ( floor )

                data TooShort

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floor else TooShort
                    h
                }
                """)));
    }

    /** A published value building a third module's type. What a published *helper* builds of a third
     * module's type stays the reader's to declare — the publisher hands over only what it declares —
     * but a value hands over nothing: it was built where the value is defined, and the behavior
     * naming it is no more the maker for a type declared elsewhere than for one declared here. */
    @Test
    void aPublishedValueBuildingAThirdModulesTypeIsCarriedToo() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module money exposing ( Yen )

                data Yen = Int
                """, """
                module pricing exposing ( standard )

                import money ( Yen )

                let standard = Yen(1000)
                """, """
                module order exposing ( Receipt, bill )

                import money ( Yen )
                import pricing ( standard )

                data Receipt = { total: Yen }

                behavior bill : (n: Int) -> Receipt constructs Receipt
                let bill (n) = Receipt { total = standard }
                """)));
    }

    /** Carried, not absent: an author who writes the authority is not told the behavior builds
     * nothing, the same answer a construction arriving in a published body gets. */
    @Test
    void theAuthorityMayStillBeDeclared() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorHours = Hours(20.0m)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort, Hours
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** A recursive helper is lowered to a method rather than expanded, so a value reaching one
     * leaves a call standing where the constructions would have been. What the value made is the
     * value's either way — whether a helper on the way could be expanded into it is not something
     * the reading behavior's declaration should turn on. */
    @Test
    void aValueReachingARecursiveHelperCarriesWhatItBuilds() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                partial let makeFloor (n: Int) : Hours =
                    if n == 0 then Hours(20.0m) else makeFloor(n - 1)

                partial let floorHours = makeFloor(1)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** The same helper called by the behavior itself. The mark is on the call the value brought in,
     * not on the helper, so one module may do both and each call answers for what it is. */
    @Test
    void callingThatRecursiveHelperDirectlyStillNeedsAuthority() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                partial let makeFloor (n: Int) : Hours =
                    if n == 0 then Hours(20.0m) else makeFloor(n - 1)

                partial let floorHours = makeFloor(1)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    makeFloor(2)
                }
                """));

        assertEquals("E1002", e.code(), e.getMessage());
    }

    /** A value reached through values of the same module. The mark is written over the whole
     * expansion by the substitution no other substitution is inside, so what it says of a
     * construction does not depend on how many names stood between the behavior and it. */
    @Test
    void aValueReachedThroughValuesOfThisModuleCarriesTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let baseHours = Hours(20.0m)
                let namedHours = baseHours
                let floorHours = namedHours

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** The same, with a helper expanded on the way. A helper call becomes an expansion, whose
     * `given` is not a slot of the walk that rebuilds an expression, so this is the shape that says
     * the outermost substitution reaches what the ones under it produced. */
    @Test
    void aValueReachedThroughAValueThatExpandsAHelperCarriesTheSameWay() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorOf (d) = Hours(d)
                let baseHours = floorOf(20.0m)
                let floorHours = baseHours

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """));
    }

    /** A unit data is constructed by being named, so it has no construction node to carry the mark
     * — the name carries it. A value standing for one reaches the reading behavior by that path. */
    @Test
    void aUnitDataNamedByAValueIsCarriedToo() {
        assertDoesNotThrow(() -> Compiler.compile("""
                module m

                data Marker
                data In = { n: Int }
                data Out = { n: Int }

                let mark = Marker

                behavior go : (i: In) -> Out | Marker
                    constructs Out
                let go (i) = if i.n > 0 then Out { n = i.n } else mark
                """));
    }

    /** A behavior that writes the construction itself still answers for it. */
    @Test
    void constructingTheLimitInTheBodyStillNeedsAuthority() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= Hours(20.0m) else TooShort
                    h
                }
                """));

        assertEquals("E1002", e.code(), e.getMessage());
    }

    /** A helper body is checked as though it had been written inline, so what it builds is the
     * caller's. That is what tells a helper from a behavior, and it is unchanged. */
    @Test
    void aHelperThatBuildsTheLimitStillChargesItsCaller() {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorOf (d) = Hours(d)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorOf(20.0m) else TooShort
                    h
                }
                """));

        assertEquals("E1002", e.code(), e.getMessage());
    }

    /** The limit is read at run time, not merely accepted by the checker. */
    @Test
    void theLimitIsCompared() throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile("""
                module m

                data Hours = Decimal invariant value >= 0.0m
                data TooShort

                let floorHours = Hours(20.0m)

                behavior judge : (h: Hours) -> Hours | TooShort
                    constructs TooShort
                let judge (h) = {
                    guard h >= floorHours else TooShort
                    h
                }
                """), getClass().getClassLoader());

        Object behavior = Emitted.behavior(loader, "m", "judge").getConstructor().newInstance();

        Object kept = Codecs.apply(behavior, Codecs.decoded(loader, "m.Hours", new java.math.BigDecimal("40.0")));
        assertEquals(new java.math.BigDecimal("40"), Codecs.encode(loader, "m.Hours", kept),
                "written as the amount, the scale it arrived with being no part of it");

        Object rejected = Codecs.apply(behavior, Codecs.decoded(loader, "m.Hours", new java.math.BigDecimal("10.0")));
        assertEquals("TooShort", rejected.getClass().getSimpleName());
    }
}
