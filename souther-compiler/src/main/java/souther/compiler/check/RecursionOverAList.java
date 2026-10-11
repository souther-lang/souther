package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.types.Refinement;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * A recursive helper that walks a list by its head: its body is a {@code match} on the element at
 * index nought of one of its parameters, answering one thing where there is none, and where there is
 * one, something that calls the helper again only on the elements from index one on, with every
 * other parameter as it was handed.
 *
 * <p>What a reader may take of one is that on a list holding something it answers what the present
 * arm answers with the element at nought standing for its binding and each call of itself answering
 * what the helper answers on the rest — and that what the rest holds and the element at nought are
 * all the list holds. So a statement that holds of the answer exactly where the present arm's answer
 * holds of some element, or of every one, holds of the helper's answer the same way over the whole
 * list. Whether the recursion ends is not part of it: a run that does not end answers nothing.
 *
 * <p>Read by what the operations are, never by what they are called. The element at an index is
 * read with what the library's own walk reads one with, and the rest of the list is an operation the
 * library is proved to answer the elements of its list from an index on with
 * ({@link BoundOperationFact.HoldsTheElementsFrom}), handed one.
 *
 * @param walked  the parameter the list is handed on
 * @param none    the arm taken where the list holds nothing
 * @param some    the arm taken where it holds something
 * @param element the binding the arm taken where it holds something names its head by
 * @param again   every call of itself the arm taken where it holds something makes, each on the
 *                rest of the list
 */
public record RecursionOverAList(int walked, Core.Case none, Core.Case some,
                                 Core.Binder element, List<Core.Call> again) {

    public RecursionOverAList {
        again = List.copyOf(again);
    }

    /**
     * What {@code body}, the body of {@code self}, walks — or null where it is not a walk of a list
     * by its head.
     */
    public static RecursionOverAList of(ValueName.Helper self, CalledBody body) {
        if (!(Core.withoutStanding(body.body()) instanceof Core.Match match)
                || match.cases().size() != 2
                || !(AnOperationApplied.of(match.scrutinee()) instanceof AnOperationApplied(
                        ValueName operation, List<Core> args))
                || !operation.equals(Reductions.readsTheElementAtAnIndex())
                || args.size() != 2 || !isWhole(args.get(0), 0)) {
            return null;
        }
        int walked = parameterAt(args.get(1), body.parameters());
        Core.Case none = null;
        Core.Case some = null;
        for (Core.Case arm : match.cases()) {
            if (arm.binding() instanceof Core.ArmBinding.Payload) {
                some = arm;
            } else if (arm.pattern() instanceof Core.ResolvedPattern.Single one
                    && one.selected().refinement() instanceof Refinement.OptionAbsent) {
                none = arm;
            }
        }
        if (walked < 0 || none == null || some == null || some.binder() == null
                || some.binder().binding() == null || callsItself(none.body(), self)) {
            return null;
        }
        List<Core.Call> again = new ArrayList<>();
        callsOf(some.body(), self, again);
        for (Core.Call call : again) {
            if (!onTheRest(call, walked, body.parameters())) {
                return null;
            }
        }
        return new RecursionOverAList(walked, none, some, some.binder(), again);
    }

    /** Whether {@code call} hands the parameter at {@code walked} the elements of what it was
     *  handed from index one on, and every other parameter what it was handed. */
    private static boolean onTheRest(Core.Call call, int walked, List<Core.Binder> parameters) {
        if (call.args().size() != parameters.size()) {
            return false;
        }
        for (int at = 0; at < parameters.size(); at++) {
            Core arg = call.args().get(at);
            if (at != walked ? parameterAt(arg, parameters) != at : !fromIndexOne(arg, walked,
                    parameters)) {
                return false;
            }
        }
        return true;
    }

    /** Whether {@code arg} is the elements of the parameter at {@code walked} from index one on. */
    private static boolean fromIndexOne(Core arg, int walked, List<Core.Binder> parameters) {
        if (!(AnOperationApplied.of(arg) instanceof AnOperationApplied(
                ValueName operation, List<Core> args))) {
            return false;
        }
        BoundOperationFact.HoldsTheElementsFrom from =
                DefaultBoundOperationFacts.get().holdsTheElementsFrom(operation);
        return from != null && isWhole(args.get(from.count().position()), 1)
                && parameterAt(args.get(from.list().position()), parameters) == walked;
    }

    /** Which of {@code parameters} {@code e} names as it was handed, or -1 where it names none. */
    static int parameterAt(Core e, List<Core.Binder> parameters) {
        if (!(Core.withoutStanding(e) instanceof Core.Read read) || read.binding() == null) {
            return -1;
        }
        for (int at = 0; at < parameters.size(); at++) {
            Core.Binder parameter = parameters.get(at);
            if (parameter != null && read.binding().equals(parameter.binding())) {
                return at;
            }
        }
        return -1;
    }

    private static boolean isWhole(Core e, long value) {
        return Core.withoutStanding(e) instanceof Core.Int written && written.value() == value;
    }

    /** Whether {@code self} is called anywhere in {@code e}. */
    private static boolean callsItself(Core e, ValueName.Helper self) {
        List<Core.Call> calls = new ArrayList<>();
        callsOf(e, self, calls);
        return !calls.isEmpty();
    }

    /** Every call of {@code self} in {@code e}, into {@code out}. */
    static void callsOf(Core e, ValueName.Helper self, List<Core.Call> out) {
        if (e instanceof Core.Call call && call.fn() instanceof Core.Reached.OfDeclaration reached
                && self.equals(reached.denotes())) {
            out.add(call);
        }
        Core.forEachChild(e, child -> callsOf(child, self, out));
    }
}
