package souther.compiler.query;

import souther.compiler.core.ValueShape;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A rule a spread brings in from another module runs as the module that wrote it settled it.
 *
 * <p>What a clause states is settled per module: a helper the clause names is expanded into it. A
 * module publishes the type and not every definition its rules are written over, so a reader handed
 * the clause as resolution left it is handed a name that means nothing where it stands — and the
 * reading that runs would be elaborating something no author wrote.
 *
 * <p>Held at the reading that runs, because that is the consumer of the settled form: what a value
 * is checked against when it is built. The other representation a clause has is read from
 * {@code ExpandedClauseLookup}, which answers by declaration and cannot be handed a node.
 *
 * <p>Compared against what the declaring module's own reading runs, rather than against a shape.
 * What is being held is that a rule is its declaration's wherever it is read, not that today's
 * expansion comes out one particular way.
 *
 * <p><b>What this pins is behaviour that already holds, and it is written down for that reason.</b>
 * Reading a declaration from a world at the wrong stage breaks every reader of it, this module's
 * own included, so no degradation of the world tells the two apart — which is to say the ownership
 * here is not held up by anything a run can observe. What holds it is the shape of the walk: the
 * declarations it reaches come from one world and what they state comes from one owner, and that is
 * held where it can be, over the surface rather than over a run.
 */
class AnInheritedRuleRunsAsItsOwnModuleSettledItTest {

    private static final TypeSymbol.AtModule THE_SPREAD =
            TypeSymbols.declared(new TypeKey("wrote", "Base"));

    private static final TypeSymbol.AtModule THE_TAKER =
            TypeSymbols.declared(new TypeKey("reads", "Wider"));

    /** The rule is written over a definition of this module, which the module does not publish. */
    private static final String DECLARING = """
            module wrote exposing ( Base )

            let floor = 0

            data Base = { n: Int }
                invariant atLeast = n >= floor
            """;

    /** Takes the rule in with the fields, so what it holds of a value is the other module's. */
    private static final String READING = """
            module reads

            import wrote ( Base )

            data Wider = { ...Base, m: Int }
            """;

    private static Compilation compiled() {
        Compilation c = Compilation.ofSources(List.of(DECLARING, READING), ModulePath.EMPTY);
        c.answerEverything();
        assertEquals(List.of(), c.db().allReports(), "the workspace compiles to begin with");
        return c;
    }

    /** What the reading that runs holds a value of {@code named} to. */
    private static List<ValueShape.Invariant> runsAgainst(Compilation c,
                                                          TypeSymbol.AtModule named) {
        Answer<Map<TypeSymbol.AtModule, ValueShape>> shapes =
                c.db().ask(new Shapes.ValueShapes(named.module()));
        assertNotNull(shapes.value(), () -> named.module() + " has a reading that runs");
        ValueShape shape = shapes.value().get(named);
        assertNotNull(shape, () -> named + " is read there");
        return shape.invariants();
    }

    @Test
    void aRuleTakenInFromAnotherModuleRunsAsThatModuleSettledIt() {
        Compilation c = compiled();

        List<ValueShape.Invariant> wrote = runsAgainst(c, THE_SPREAD);
        assertFalse(wrote.isEmpty(), "the declaration under test states a rule");

        assertEquals(wrote.toString(), runsAgainst(c, THE_TAKER).toString(),
                "the rule a spread brings in is the one its own module settled");
    }

    /**
     * And the settling rewrites that rule, which is what makes the check above say something.
     *
     * <p>Were the clause left alone — the bound written out, the definition it names exposed — every
     * reading of it would agree and the check above would hold of a compiler that never settled
     * anything.
     */
    @Test
    void theRuleUnderTestIsOneTheSettlingRewrites() {
        Compilation c = compiled();

        Answer<souther.compiler.check.Normalized.Def> settled =
                c.db().ask(new Shapes.NormalizedDef(THE_SPREAD.key()));
        Answer<souther.compiler.ast.Hir.Def> resolved =
                c.db().ask(new Names.ResolvedDeclaration(THE_SPREAD.key()));
        assertNotNull(settled.value(), "the declaration under test is normalized");
        assertNotNull(resolved.value(), "the declaration under test is resolved");

        assertFalse(clausesOf(settled.value().node()).equals(clausesOf(resolved.value())),
                "the rule under test is one the settling rewrites");
    }

    private static String clausesOf(souther.compiler.ast.Hir.Def def) {
        StringBuilder out = new StringBuilder();
        for (souther.compiler.ast.Hir.InvariantClause clause
                : ((souther.compiler.ast.Hir.Data) def).invariants()) {
            out.append(clause.expr()).append('\n');
        }
        return out.toString();
    }
}
