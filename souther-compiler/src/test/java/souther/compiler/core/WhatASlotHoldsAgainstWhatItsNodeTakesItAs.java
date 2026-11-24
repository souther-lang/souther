package souther.compiler.core;

import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a node says what type a slot of it takes its value at, whether the value in the slot is of
 * that type. A fork answers what its branches join at, and each branch is of that type; a list
 * holds its elements at the type it is a list of; a binding holds its value at the type it is in
 * force at and answers what its body answers; an optional holds what it holds at the type it is
 * an optional of; {@code ++} over lists takes both sides at the list it answers; a kernel's
 * application takes each argument at what it settled it takes it as.
 *
 * <p>Asked of a node and not of a population, so that a test of one model and a test of every
 * model hold the same rule.
 */
final class WhatASlotHoldsAgainstWhatItsNodeTakesItAs {

    private WhatASlotHoldsAgainstWhatItsNodeTakesItAs() {
    }

    /** What {@code node} says of a slot's type that the value in the slot does not have. */
    static List<String> disagreements(Core node) {
        List<String> out = new ArrayList<>();
        switch (node) {
            case Core.If fork -> {
                expect(out, fork, "then", fork.type(), fork.then());
                expect(out, fork, "else", fork.type(), fork.els());
            }
            case Core.IfConstructed attempt -> {
                expect(out, attempt, "then", attempt.type(), attempt.then());
                attempt.els().forEach(arm -> expect(out, attempt, "else", attempt.type(),
                        arm.body()));
            }
            case Core.Match match -> match.cases().forEach(arm ->
                    expect(out, match, "arm", match.type(), arm.body()));
            case Core.ListLit list when list.type() instanceof Type.ListOf of ->
                    list.elements().forEach(each -> expect(out, list, "element", of.element(), each));
            case Core.LetIn let -> {
                expect(out, let, "value", let.bindType(), let.value());
                expect(out, let, "body", let.type(), let.body());
            }
            case Core.OptionSome some when some.type() instanceof Type.OptionOf of ->
                    expect(out, some, "value", of.element(), some.value());
            case Core.Binary joined when joined.op() == BinOp.CONCAT
                    && joined.type() instanceof Type.ListOf -> {
                expect(out, joined, "left", joined.type(), joined.left());
                expect(out, joined, "right", joined.type(), joined.right());
            }
            case Core.Call call when call.settlement()
                    instanceof Core.CallSettlement.AtKernel(List<Type> takes, _) -> {
                if (takes.size() != call.args().size()) {
                    out.add("Call at " + call.pos() + ": `" + call.name() + "` takes "
                            + takes.size() + " argument(s) and holds " + call.args().size());
                } else {
                    for (int i = 0; i < takes.size(); i++) {
                        expect(out, call, "argument " + (i + 1) + " of `" + call.name() + "`",
                                takes.get(i), call.args().get(i));
                    }
                }
            }
            default -> { }
        }
        return out;
    }

    private static void expect(List<String> out, Core node, String slot, Type takes, Core value) {
        if (value != null && !takes.equals(value.type())) {
            out.add(node.getClass().getSimpleName() + " at " + node.pos() + ": its " + slot
                    + " is taken as " + Type.show(takes) + " and holds "
                    + Type.show(value.type()));
        }
    }
}
