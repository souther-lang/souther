package souther.compiler.coverage;

import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.Lower;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * The fork a coverage obligation is about is the fork the lowering builds.
 *
 * <p>A comprehension's guards become forks, and two readers number them. The lowering builds them,
 * walking the guards from the last to the first because each stands over the one after it; the
 * reading that decides who a fork's decision belongs to runs before that lowering, where a rule the
 * caller supplied is still a parameter, and walks them from the first to the last. An obligation
 * named for a fork the lowering did not build is about nothing, and what says it is not is that the
 * two number one guard alike.
 *
 * <p>So both are run here and their answers put together. Each guard rests on a different supplied
 * rule, so what the reading says about a fork names which guard it read — which is what tells a
 * numbering that is off by a place from one that merely disagrees about the set.
 */
class WhatTheReadingNamesIsTheForkTheLoweringBuildsTest {

    private static final SourcePos AT = new SourcePos(1, 1);

    private static final String MODULE = "m";

    private static final ReachName.Declaration DECLARATION =
            new ReachName.Own(new ValueName.Helper(MODULE, "f"));

    @Test
    void theForkTheReadingNamesForAGuardIsTheOneTheLoweringPutOnIt() {
        List<String> rules = List.of("r0", "r1", "r2");
        Hir.FnDef fn = aHelperGuardedByEachOf(rules);
        Hir.ListComp comp = comprehensionOf(fn);

        Map<SourceConstructOrigin, DecisionSource> read =
                DecisionSources.of(Map.of(), Map.of(DECLARATION, fn)).byFork();
        List<SourceConstructOrigin> built = forksBuiltFor(comp);

        List<String> namedByTheReading = new ArrayList<>();
        for (SourceConstructOrigin fork : built) {
            namedByTheReading.add(ruleOf(read.get(fork)));
        }
        assertEquals(rules, namedByTheReading,
                "the guard the lowering built a fork for is the guard the reading named it for:"
                        + " a numbering off by a place leaves an obligation about a branch that is"
                        + " not there");
    }

    /** Which rule the reading says a fork's decision was supplied by. */
    private static String ruleOf(DecisionSource said) {
        DecisionSource.Supplied supplied = assertInstanceOf(DecisionSource.Supplied.class, said,
                "a guard that reads a supplied rule is decided by whoever supplied it");
        assertEquals(1, supplied.parameters().size(), "each guard here reads one rule");
        return supplied.parameters().get(0);
    }

    /** The origins the lowering put on the {@code if} it built for each guard, outermost first —
     *  which is the first guard, an earlier guard standing over a later one. */
    private static List<SourceConstructOrigin> forksBuiltFor(Hir.ListComp comp) {
        List<SourceConstructOrigin> out = new ArrayList<>();
        Hir.Expr lowered = Lower.desugarExpr(comp);
        while (lowered instanceof Hir.If branch) {
            out.add(branch.origin());
            lowered = branch.then();
        }
        return out;
    }

    /** {@code let f (r0, r1, ...) = [ 1 | r0, r1, ... ]}, each guard reading one supplied rule. */
    private static Hir.FnDef aHelperGuardedByEachOf(List<String> rules) {
        List<Hir.FnParam> params = new ArrayList<>();
        List<Hir.Expr> guards = new ArrayList<>();
        for (int i = 0; i < rules.size(); i++) {
            Hir.Binder binder = new Hir.Binder(WrittenName.synthetic(rules.get(i), AT),
                    new BindingId(new BindingOwner.OfValue(MODULE, "f"), i), AT);
            params.add(new Hir.FnParam(binder, aRuleType(), false));
            guards.add(Hir.Var.local(binder, AT));
        }
        Hir.ListComp comp = new Hir.ListComp(new Hir.IntLit(1, AT, null), guards,
                SourceConstructOrigin.written(MODULE, 0, SourceConstruct.COMPREHENSION), AT, null);
        return new Hir.FnDef(WrittenName.synthetic("f", AT), MODULE, params, null,
                new Hir.FnBody.Written(comp), new Hir.Modifiers(false, false),
                DefinitionRole.Ordinary.INSTANCE, AT);
    }

    private static Hir.ListComp comprehensionOf(Hir.FnDef fn) {
        return (Hir.ListComp) ((Hir.FnBody.Written) fn.body()).expr();
    }

    /** A parameter of function type, which is what a rule the caller supplies is. */
    private static Hir.RetType aRuleType() {
        return new Hir.RetType(List.of(new Hir.FnType(List.of(), null, AT)), AT);
    }
}
