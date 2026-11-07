package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ReachName;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A fork resting on a rule is reported under the rule's name, found from the slot it stands at among
 * all the parameters.
 *
 * <p>The parameters here alternate between data and rules, so a slot counted among the rules alone
 * would name the wrong parameter: {@code second} stands at slot 3 and is the second rule. Each guard
 * rests on a different set, and the one resting on both reads them in the opposite order to the one
 * they are declared in.
 */
class TheRulesAForkRestsOnAreNamedBySlotAmongAllTheParametersTest {

    private static final SourcePos AT = new SourcePos(1, 1);

    private static final String MODULE = "m";

    private static final ReachName.Declaration DECLARATION =
            new ReachName.Own(new ValueName.Helper(MODULE, "f"));

    @Test
    void aRuleIsNamedByItsPlaceAmongAllTheParametersAndInTheOrderDeclared() {
        Hir.FnDef fn = aHelperWithRulesBetweenData();

        Map<SourceConstructOrigin, DecisionSource> read =
                DecisionSources.of(DefaultStdlib.get(), Map.of(), Map.of(DECLARATION, fn)).byFork();

        Hir.ListComp comp = (Hir.ListComp) ((Hir.FnBody.Written) fn.body()).expr();
        List<List<String>> named = new ArrayList<>();
        for (int guard = 0; guard < comp.guards().size(); guard++) {
            DecisionSource.Supplied supplied = assertInstanceOf(DecisionSource.Supplied.class,
                    read.get(comp.forkOfGuard(guard)), "each guard reads a supplied rule");
            named.add(supplied.parameters());
        }
        assertEquals(List.of(List.of("second"), List.of("first", "second"), List.of("first")),
                named,
                "a guard on the second rule alone is slot 3, and one on both is reported as"
                        + " declared whichever it read first");
    }

    /** {@code let f (x, first, y, second) = [ 1 | second, second && first, first ]}. */
    private static Hir.FnDef aHelperWithRulesBetweenData() {
        List<String> names = List.of("x", "first", "y", "second");
        List<Hir.Binder> binders = new ArrayList<>();
        List<Hir.FnParam> params = new ArrayList<>();
        for (int slot = 0; slot < names.size(); slot++) {
            Hir.Binder binder = new Hir.Binder(WrittenName.synthetic(names.get(slot), AT),
                    new BindingId(new BindingOwner.OfValue(MODULE, "f"), slot), AT);
            binders.add(binder);
            params.add(new Hir.FnParam(binder, slot % 2 == 1 ? aRuleType() : aDataType()));
        }
        Hir.Expr first = Hir.Var.local(binders.get(1), AT);
        Hir.Expr second = Hir.Var.local(binders.get(3), AT);
        SourceConstructOrigin origin = SourceConstructOrigin.written(
                new WrittenOwner.Body(MODULE, "b"), 0, SourceConstruct.COMPREHENSION);
        Hir.Expr both = new Hir.Binary(BinOp.AND, second, first, origin, AT, null);
        Hir.ListComp comp = new Hir.ListComp(new Hir.IntLit(1, AT, null),
                List.of(second, both, first), origin, AT, null);
        return new Hir.FnDef(WrittenName.synthetic("f", AT), MODULE, params, null,
                new Hir.FnBody.Written(comp), new Hir.Modifiers(false, false),
                DefinitionRole.Ordinary.INSTANCE, AT);
    }

    /** A parameter of function type, which is what a rule the caller supplies is. */
    private static Hir.RetType aRuleType() {
        Hir.RetType answers = Hir.RetType.of(List.of(Hir.TypeRef.of(Type.BOOL, AT)), AT);
        return Hir.RetType.of(List.of(new Hir.FnType(List.of(), answers, AT)), AT);
    }

    /** A parameter of any other type, which is data for the declaration's own rule to read. */
    private static Hir.RetType aDataType() {
        return Hir.RetType.of(List.of(Hir.TypeRef.of(Type.BOOL, AT)), AT);
    }
}
