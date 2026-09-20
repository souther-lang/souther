package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.OccurrenceLineage;
import souther.compiler.types.MaterialisationSite;
import souther.compiler.types.RegionSlot;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A value built for two regions is two builds of one written body, and they are two occurrences.
 *
 * <p>Everything that files an answer about a construct addresses it by what the source wrote and
 * which copies it stands in, and one enumeration of a module's comparisons refuses a place two of
 * its nodes share. A value named on paths that share no region is built once per region, so what
 * tells those builds apart has to be in the address — wherever the regions are: two behaviors, two
 * forks of one, the right of a short-circuit, and a value whose own fork names another.
 *
 * <p>The model states one rule where a value is named, however many builds the compiler made of it,
 * so the builds are two occurrences of one construct of the model.
 */
class AValueBuiltForTwoRegionsIsTwoOccurrencesTest {

    private static final String HEAD = """
            module m exposing (f, g, Kind, Amount)

            data Kind = Yes | No

            data Amount = Int invariant value >= 0

            let inner = List.length([1, 2, 3]) > 2

            let outer = if List.length([1]) > 0 then inner else false

            behavior g : (n: Int) -> Bool
            let g (n) = n > 1

            """;

    private static void accepted(String tail) {
        assertEquals("{0=[]}", String.valueOf(Compiler.compiled(HEAD + tail, "m").diagnostics()));
    }

    @Test
    void twoBehaviorsThatEachNameOneValue() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = inner
                """);
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoForks() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (if n > 0 then inner else false) || (if n > 1 then inner else false)
                """);
    }

    @Test
    void oneValueNamedOnTheRightOfTwoShortCircuits() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (n > 0 && inner) || (n > 1 && inner)
                """);
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoMatches() {
        accepted("""
                behavior f : (k: Kind) -> Bool
                let f (k) =
                  (match k with | Yes -> inner | No -> false)
                  || (match k with | Yes -> false | No -> inner)
                """);
    }

    @Test
    void oneValueNamedInAnArmOfEachOfTwoAttemptedConstructions() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) =
                  (if Amount(n) as a then inner else false)
                  || (if Amount(n - 1) as b then false else inner)
                """);
    }

    @Test
    void aValueInAComprehensionGuardAndInAnArm() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) =
                  List.length([n | inner, n > 0]) > 0 || (if n > 1 then inner else false)
                """);
    }

    @Test
    void aValueWhoseOwnForkNamesAnotherBuiltForTwoRegions() {
        accepted("""
                behavior f : (n: Int) -> Bool
                let f (n) = (if n > 0 then outer else false) || (if n > 1 then outer else false)
                """);
    }


    private static final WrittenOwner.Body OWNER = new WrittenOwner.Body("m", "f");

    private static final ValueName VALUE = new ValueName.Helper("m", "inner");

    private static MaterialisationSite armOf(int fork, RegionSlot slot) {
        return new MaterialisationSite.Slot(
                SourceConstructOrigin.written(OWNER, fork, SourceConstruct.IF), slot);
    }

    private static ConstructOccurrence builtFor(MaterialisationSite site) {
        return new ConstructOccurrence(
                SourceConstructOrigin.written(new WrittenOwner.Body("m", "inner"), 0,
                        SourceConstruct.BINARY),
                OccurrenceLineage.ORIGINAL.builtFor(VALUE, site));
    }

    @Test
    void twoBuildsOfOneConstructAreTwoOccurrences() {
        ConstructOccurrence first = builtFor(armOf(0, new RegionSlot.IfThen()));
        ConstructOccurrence second = builtFor(armOf(1, new RegionSlot.IfThen()));

        assertNotEquals(first, second);
    }

    @Test
    void theModelStatesOneConstructWhereTwoBuildsWereMade() {
        ConstructOccurrence first = builtFor(armOf(0, new RegionSlot.IfThen()));
        ConstructOccurrence second = builtFor(armOf(1, new RegionSlot.IfThen()));

        assertEquals(ModelOccurrence.statedAt(first), ModelOccurrence.statedAt(second));
    }
}
