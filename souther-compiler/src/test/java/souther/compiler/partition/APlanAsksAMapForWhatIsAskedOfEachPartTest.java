package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.DeclaredBounds;
import souther.compiler.check.Prepared;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.Requirements;
import souther.compiler.inputs.TermPath;
import souther.compiler.meta.ModulePath;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;
import souther.compiler.query.Shapes;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A plan for a row asks a map for what is asked of each of its parts, and of no other.
 *
 * <p>A map holds a value under a key, and a class at one is no demand on the other. A row asked to
 * hold a key in a class holds it over a value the rules admit, so nothing about how that value is
 * made is planned — and a value nested deeper than a plan descends is not a reason for the key's
 * row to be any harder to build.
 */
class APlanAsksAMapForWhatIsAskedOfEachPartTest {

    private static final ConstructionPlan.HowManyItHolds ANY =
            (_, _) -> new DeclaredBounds.CountRange(0, Integer.MAX_VALUE);

    private static final String DEEP_VALUES = """
            module g

            data L3 = { v: Int }
            data L2 = { down: L3 }
            data L1 = { down: L2 }

            data Usage = { counts: Map<String, L1> }
            data Page = { count: Int }

            behavior readArticles : (u: Usage) -> Page
            """;

    private static final TermPath COUNTS = TermPath.of("u").then("counts");

    /** A key fixed: the map is planned at its key alone. */
    @Test
    void aKeyAskedForPlansTheKeyAndNotTheValue() {
        ConstructionPlan plan = planned(Set.of(COUNTS.key()));
        ConstructionPlan.Held held = assertInstanceOf(ConstructionPlan.Held.class,
                plan.at(COUNTS), "the map is built around what it is asked to hold");
        assertTrue(held.key().isPresent(), "the key is a position of the plan");
        assertTrue(held.under().isEmpty(), () -> "and the value under it is none: " + held);
        assertEquals(List.of(COUNTS.key()),
                plan.slots().stream().map(ConstructionPlan.Slot::at).toList(),
                "so the one place a value is chosen at is the key");
    }

    /** A value fixed: the map is planned at its value, and its key is whatever keeps entries apart. */
    @Test
    void aValueAskedForPlansTheValueAndNotTheKey() {
        TermPath deep = COUNTS.element().then("down").then("down").then("v");
        ConstructionPlan plan = planned(Set.of(deep));
        ConstructionPlan.Held held = assertInstanceOf(ConstructionPlan.Held.class,
                plan.at(COUNTS), "the map is built around what it is asked to hold");
        assertTrue(held.under().isPresent(), "the value is planned");
        assertTrue(held.key().isEmpty(), () -> "and no key is: " + held);
    }

    private static ConstructionPlan planned(Set<TermPath> decided) {
        Read read = readOf();
        Symbols symbols = read.symbols();
        ConstructionPlan.Result result = ConstructionPlan.of(read.declared(), TermPath.of("u"),
                ScopedDeclarations.wrapsOf(symbols), symbols, ScopedDeclarations.kindsOf(symbols),
                ScopedDeclarations.sumsOf(symbols), decided, Requirements.NONE,
                ConstructionPlan.ContentsComposed.NONE, ANY);
        return assertInstanceOf(ConstructionPlan.Result.Planned.class, result,
                () -> "a plan is made: " + result).plan();
    }

    private record Read(Type declared, Symbols symbols) {}

    private static Read readOf() {
        Compilation compilation = Compilation.ofSources(List.of(DEEP_VALUES), ModulePath.EMPTY);
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(module)).value();
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(module)).value();
        Hir.SpecBehavior spec = (Hir.SpecBehavior) prepared.behaviors().stream()
                .filter(b -> b.name().equals("readArticles")).findFirst().orElseThrow();
        return new Read(sigs.get(spec.name()).inputTypes().get(0),
                Scopes.derived(compilation.db(), module).value());
    }
}
