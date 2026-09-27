package souther.compiler.check;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.query.Compilation;
import souther.compiler.query.Shapes;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The entry a fixture reads a named value through, decided once at the surface a module's rows and
 * values are minted from.
 *
 * <p>Two answers and never a third: a value another module may call already has one — {@link
 * ValueEntries}'s, and the fixture reuses it — and a value nothing but a fixture reaches gets one of
 * its own ({@link FixtureValueEntries}), never both.
 */
class AFixtureEntryIsMintedOnlyWhereNoPublishedOneAlreadyAnswersTest {

    private static final String MODULE = """
            module m exposing ( settle%s )

            data Amount = Decimal
            data Order = { total: Amount }
            data Accepted
            data Rejected

            let baseline = Order { total = Amount(1.5m) }

            behavior settle : (o: Order) -> Accepted | Rejected

            let settle (o) = if o.total == Amount(1.5m) then Accepted else Rejected

            example settle
                | "a baseline" : (baseline) -> Accepted
            """;

    @Test
    void aPrivateBaselineGetsAFixtureValueEntryAndNoPublishedOne() {
        CheckSurface surface = surfaceOf(MODULE.formatted(""));
        ValueName.Helper baseline = new ValueName.Helper("m", "baseline");

        String method = surface.fixtureValueMethods().get(baseline);
        assertNotNull(method, "a row named the value, so a fixture entry answers for it");
        assertEquals(FixtureValueEntries.methodFor("m.baseline"), method);

        Hir.FnDef entry = mintedAs(surface, method);
        assertNotNull(entry, "the minted definitions carry the entry the correspondence names");
        assertTrue(entry.role() instanceof DefinitionRole.FixtureValueEntry,
                "a private value's fixture entry, never a published one — nothing exposes `baseline`");
    }

    @Test
    void aPublishedBaselineReusesItsPublishedEntryRatherThanMintingASecondOne() {
        CheckSurface surface = surfaceOf(MODULE.formatted(", baseline"));
        ValueName.Helper baseline = new ValueName.Helper("m", "baseline");

        assertEquals(ValueEntries.methodFor("baseline"), surface.fixtureValueMethods().get(baseline),
                "the fixture reads the same entry another module would call, not a second one");

        long fixtureEntriesForBaseline = surface.mintedDefs().stream()
                .filter(def -> def.role() instanceof DefinitionRole.FixtureValueEntry fve
                        && fve.of().equals(baseline))
                .count();
        assertEquals(0, fixtureEntriesForBaseline,
                "a published value's fixture entry is the published one, not a second mint");
    }

    /**
     * A value buried inside a row's own operand — an argument, never the operand itself — gets no
     * entry, and so is never asked to write a type it would otherwise be let keep unwritten.
     *
     * <p>{@code inc} here is exactly the value {@link
     * souther.compiler.CompileExposedValueTest#anUnpublishedValueIsNotAskedForItsTypeWhateverItIsRunAs}
     * pins as never needing one, applied inside the row's operand rather than named by it. Minting an
     * entry for it anyway — which {@link FixtureValueEntries#referencedValues} once did, by reading
     * past the top of the operand — would ask it to write a function type where nothing else does,
     * turning an argument to an otherwise ordinary computed row into a refusal.
     */
    @Test
    void aValueAppliedInsideARowsOperandGetsNoEntry() {
        CheckSurface surface = surfaceOf("""
                module m exposing ( use )

                let adder (n: Int) = (x) -> x + n
                let inc = adder(1)

                let applyTo (f: (Int) -> Int, x: Int) = f(x)

                behavior use : (n: Int) -> Int

                let use (n) = n

                example use
                    | "computed input" : (applyTo(inc, 1)) -> 2
                """);

        ValueName.Helper inc = new ValueName.Helper("m", "inc");
        assertNull(surface.fixtureValueMethods().get(inc),
                "`inc` is an argument the row's operand applies, not a name the row itself is");
    }

    private static Hir.FnDef mintedAs(CheckSurface surface, String method) {
        for (Hir.FnDef def : surface.mintedDefs()) {
            if (def.name().equals(method)) {
                return def;
            }
        }
        return null;
    }

    private static CheckSurface surfaceOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        CheckSurface surface = compilation.db().ask(new Shapes.CheckSurface("m")).value();
        assertNotNull(surface, "the source under test does not get as far as being assembled");
        return surface;
    }
}
