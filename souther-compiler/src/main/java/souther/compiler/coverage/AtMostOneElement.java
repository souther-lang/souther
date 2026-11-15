package souther.compiler.coverage;

import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.core.Core;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * Whether a list expression holds at most one element on every run, read off the expression.
 *
 * <p>Yes only where the expression shows it, and no says nothing: a list this cannot read is one
 * that may hold more. What a call of a library operation does to the length is read from what the
 * library declares of the operation ({@link BoundOperationFacts}) and never from its name, so an
 * operation that builds its answer out of the elements of one argument, none of them twice, is
 * no longer than that argument whichever operation it is.
 *
 * <p>A non-recursive helper has been put in place of its call by the time a body is read, so a list
 * a helper answers is read here as the expression the helper is.
 */
final class AtMostOneElement {

    private final BoundOperationFacts facts = DefaultBoundOperationFacts.get();

    /** What the names in scope were bound to, the outer ones asked of {@code outside}. */
    private final Function<BindingId, Core> outside;

    private final Map<BindingId, Core> inside = new HashMap<>();

    private AtMostOneElement(Function<BindingId, Core> outside) {
        this.outside = outside;
    }

    /**
     * Whether {@code list} holds at most one element on every run.
     *
     * @param outside what a name bound outside {@code list} was bound to, or null where it is
     *                bound to nothing this knows of
     */
    static boolean holds(Core list, Function<BindingId, Core> outside) {
        return new AtMostOneElement(outside).of(list);
    }

    private boolean of(Core list) {
        return switch (Core.withoutStanding(list)) {
            case Core.ListLit literal -> literal.elements().size() <= 1;
            case Core.Read read -> {
                Core bound = inside.containsKey(read.binding())
                        ? inside.get(read.binding()) : outside.apply(read.binding());
                yield bound != null && of(bound);
            }
            case Core.If branch -> of(branch.then()) && of(branch.els());
            case Core.IfConstructed branch -> of(branch.then()) && branch.els().stream()
                    .allMatch(arm -> of(arm.body()));
            case Core.Match match -> match.cases().stream().allMatch(each -> of(each.body()));
            case Core.LetIn let -> {
                inside.put(let.binder().binding(), let.value());
                yield of(let.body());
            }
            case Core.Unreachable _ -> true;
            case Core.Call call -> ofACall(call);
            default -> false;
        };
    }

    /**
     * A call answers at most one where the operation builds its answer out of one argument's
     * elements and that argument holds at most one, or puts the answer together of what a closure
     * answers on each element of one and both that argument and each answer hold at most one.
     */
    private boolean ofACall(Core.Call call) {
        if (!(call.fn() instanceof Core.Reached reached)) {
            return false;
        }
        ValueName operation = reached.denotes();
        BuiltFrom<DeclaredArgument> built = facts.buildsItsResultFrom(operation);
        if (built != null) {
            return built.outputs().size() == 1
                    && built.outputs().getFirst().at().equals(ElementLineage.ResultPath.elements())
                    && built.outputs().getFirst().origin().source().elements() == 1
                    && of(call.args().get(
                            built.outputs().getFirst().origin().source().argument().position()));
        }
        BoundOperationFacts.Assembled assembled = facts.assembles(operation);
        return assembled != null
                && assembled.piece() == PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS
                && of(call.args().get(assembled.source().position()))
                && eachAnswerHoldsAtMostOne(call.args().get(assembled.closure().position()));
    }

    /** Whether what a closure answers holds at most one element wherever it is handed one. */
    private boolean eachAnswerHoldsAtMostOne(Core closure) {
        if (!(Core.withoutStanding(closure) instanceof Core.Block block)) {
            return false;
        }
        return block.body().type() instanceof Type.OptionOf || of(block.body());
    }
}
