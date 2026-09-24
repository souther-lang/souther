package souther.architecture;

import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.TypeKind;
import java.lang.classfile.attribute.CodeAttribute;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.ExceptionCatch;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.lang.classfile.instruction.StoreInstruction;
import java.lang.classfile.instruction.SwitchCase;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Which instructions a value on the stack of one method can have been made by.
 *
 * <p>The question {@link WhatBecomesOfAValueOnTheStack} asks the other way round. That one follows
 * a value forward to what takes it; this one is asked at the instruction that takes a value, and
 * answers with every instruction whose result it can be — through whatever names it was put in and
 * read back out of, through the copies the stack makes of it, and through a cast, which leaves what
 * it took.
 *
 * <p><b>Every way the code may arrive, and not the last one written.</b> A value put in a name on
 * one way through a condition is still what the name holds on the ways that missed it, so what a
 * place reads out of a name is what any way there left in it. The places are walked until no way
 * says anything new, which they reach because an answer only ever grows.
 *
 * <p>A value that came in as one of the method's parameters was made by nobody here, and is
 * answered as that parameter. What an exception handler begins with was made by whatever threw, and
 * is answered as the handler.
 */
final class WhereAValueOnTheStackCameFrom {

    /** Where a value came from: the element at {@code at}, or the parameter in slot
     *  {@code parameter} where {@code at} is negative. */
    record Origin(int at, int parameter) {

        static Origin madeAt(int at) {
            return new Origin(at, -1);
        }

        static Origin handedIn(int slot) {
            return new Origin(-1, slot);
        }

        boolean isAParameter() {
            return at < 0;
        }
    }

    /** What stands in each slot of the stack and each local, as the origins it may have. */
    private record State(List<Set<Origin>> stack, List<Set<Origin>> locals) {

        State copy() {
            List<Set<Origin>> stack = new ArrayList<>();
            this.stack.forEach(each -> stack.add(new HashSet<>(each)));
            List<Set<Origin>> locals = new ArrayList<>();
            this.locals.forEach(each -> locals.add(new HashSet<>(each)));
            return new State(stack, locals);
        }

        /** {@code other} taken into this, answering whether anything new came of it. */
        boolean absorb(State other) {
            if (stack.size() != other.stack.size()) {
                throw new IllegalStateException("two ways to one place leave the stack at two"
                        + " heights");
            }
            boolean grew = false;
            for (int i = 0; i < stack.size(); i++) {
                grew |= stack.get(i).addAll(other.stack.get(i));
            }
            for (int i = 0; i < locals.size(); i++) {
                grew |= locals.get(i).addAll(other.locals.get(i));
            }
            return grew;
        }
    }

    private final List<CodeElement> elements;

    /** What stands where each element begins, for the elements any way reaches. */
    private final Map<Integer, State> before = new HashMap<>();

    private WhereAValueOnTheStackCameFrom(List<CodeElement> elements) {
        this.elements = elements;
    }

    /** The origins of every value in {@code method}, worked out once. */
    static WhereAValueOnTheStackCameFrom of(MethodModel method) {
        CodeModel code = method.code().orElseThrow(() -> new IllegalArgumentException(
                method.methodName() + " has no code to follow a value through"));
        if (!(code instanceof CodeAttribute read)) {
            throw new IllegalArgumentException(method.methodName() + " was not read from a class"
                    + " file, so how many names it holds is not written down anywhere");
        }
        WhereAValueOnTheStackCameFrom out = new WhereAValueOnTheStackCameFrom(code.elementList());
        out.walk(entry(method, read.maxLocals()));
        return out;
    }

    /** What {@code method}'s code is, in order, which is what {@link #at} and an {@link Origin}
     *  number. */
    List<CodeElement> elements() {
        return elements;
    }

    /**
     * Where the value {@code depth} slots below the top of the stack can have come from, as the
     * element at {@code at} begins; empty where no way reaches it.
     */
    Set<Origin> at(int at, int depth) {
        State state = before.get(at);
        if (state == null) {
            return Set.of();
        }
        return Set.copyOf(state.stack().get(state.stack().size() - 1 - depth));
    }

    private static State entry(MethodModel method, int maxLocals) {
        List<Set<Origin>> locals = new ArrayList<>();
        for (int i = 0; i < maxLocals; i++) {
            locals.add(new HashSet<>());
        }
        int slot = 0;
        if (!method.flags().has(AccessFlag.STATIC)) {
            locals.get(slot).add(Origin.handedIn(slot));
            slot++;
        }
        for (ClassDesc each : method.methodTypeSymbol().parameterList()) {
            locals.get(slot).add(Origin.handedIn(slot));
            slot += TypeKind.from(each).slotSize();
        }
        return new State(new ArrayList<>(), locals);
    }

    private void walk(State start) {
        Map<Label, Integer> placed = new HashMap<>();
        List<ExceptionCatch> handlers = new ArrayList<>();
        for (int i = 0; i < elements.size(); i++) {
            if (elements.get(i) instanceof LabelTarget target) {
                placed.put(target.label(), i);
            }
            if (elements.get(i) instanceof ExceptionCatch handler) {
                handlers.add(handler);
            }
        }
        Deque<Integer> waiting = new ArrayDeque<>();
        arrive(0, start, waiting);
        while (!waiting.isEmpty()) {
            int at = waiting.pop();
            State in = before.get(at).copy();
            // What is thrown here may be caught, and the handler begins with the names as they
            // stand before this runs and with nothing but what was thrown on the stack.
            for (ExceptionCatch handler : handlers) {
                int from = placed.get(handler.tryStart());
                int to = placed.get(handler.tryEnd());
                if (from <= at && at < to) {
                    int caught = placed.get(handler.handler());
                    List<Set<Origin>> thrown = new ArrayList<>();
                    thrown.add(new HashSet<>(Set.of(Origin.madeAt(caught))));
                    arrive(caught, new State(thrown, in.copy().locals()), waiting);
                }
            }
            if (!(elements.get(at) instanceof Instruction instruction)) {
                if (at + 1 < elements.size()) {
                    arrive(at + 1, in, waiting);
                }
                continue;
            }
            State out = step(at, instruction, in);
            if (!ends(instruction) && at + 1 < elements.size()) {
                arrive(at + 1, out, waiting);
            }
            for (Label target : whereItMayGo(instruction)) {
                arrive(placed.get(target), out, waiting);
            }
        }
    }

    private void arrive(int at, State state, Deque<Integer> waiting) {
        State had = before.get(at);
        if (had == null) {
            before.put(at, state.copy());
            waiting.push(at);
        } else if (had.absorb(state)) {
            waiting.push(at);
        }
    }

    /** What stands once {@code instruction}, at {@code at}, has run on {@code in}. */
    private static State step(int at, Instruction instruction, State in) {
        List<Set<Origin>> stack = in.stack();
        List<Set<Origin>> locals = in.locals();
        switch (instruction) {
            case LoadInstruction load -> {
                if (load.typeKind() == TypeKind.REFERENCE) {
                    stack.add(new HashSet<>(locals.get(load.slot())));
                } else {
                    pushMade(stack, at, load.typeKind().slotSize());
                }
            }
            case StoreInstruction store -> {
                int slots = store.typeKind().slotSize();
                Set<Origin> stored = pop(stack, slots);
                locals.set(store.slot(), store.typeKind() == TypeKind.REFERENCE
                        ? stored : new HashSet<>());
                if (slots == 2) {
                    locals.set(store.slot() + 1, new HashSet<>());
                }
            }
            // A cast leaves what it took, said under another type.
            case TypeCheckInstruction check when check.opcode() == Opcode.CHECKCAST -> { }
            case StackInstruction rearranged -> rearrange(stack, rearranged.opcode());
            default -> {
                WhatBecomesOfAValueOnTheStack.Effect effect =
                        WhatBecomesOfAValueOnTheStack.effectOf(instruction);
                pop(stack, effect.takes());
                pushMade(stack, at, effect.leaves());
            }
        }
        return in;
    }

    private static void pushMade(List<Set<Origin>> stack, int at, int slots) {
        for (int i = 0; i < slots; i++) {
            stack.add(new HashSet<>(Set.of(Origin.madeAt(at))));
        }
    }

    /** Takes {@code slots} off the top, answering what the lowest of them held. */
    private static Set<Origin> pop(List<Set<Origin>> stack, int slots) {
        Set<Origin> lowest = new HashSet<>();
        for (int i = 0; i < slots; i++) {
            lowest = stack.removeLast();
        }
        return lowest;
    }

    /** The copies and exchanges the stack makes, each slot going where the instruction puts it. */
    private static void rearrange(List<Set<Origin>> stack, Opcode opcode) {
        int n = stack.size();
        switch (opcode) {
            case POP -> stack.removeLast();
            case POP2 -> {
                stack.removeLast();
                stack.removeLast();
            }
            case DUP -> stack.add(stack.get(n - 1));
            case DUP_X1 -> stack.add(n - 2, stack.get(n - 1));
            case DUP_X2 -> stack.add(n - 3, stack.get(n - 1));
            case DUP2 -> {
                stack.add(stack.get(n - 2));
                stack.add(stack.get(n - 1));
            }
            case DUP2_X1 -> {
                stack.add(n - 3, stack.get(n - 1));
                stack.add(n - 3, stack.get(n - 2));
            }
            case DUP2_X2 -> {
                stack.add(n - 4, stack.get(n - 1));
                stack.add(n - 4, stack.get(n - 2));
            }
            case SWAP -> {
                Set<Origin> top = stack.removeLast();
                stack.add(n - 2, top);
            }
            default -> throw new IllegalStateException(
                    "the walk cannot say what " + opcode + " does to the stack");
        }
    }

    private static boolean ends(Instruction instruction) {
        return instruction instanceof ReturnInstruction
                || instruction instanceof ThrowInstruction
                || instruction instanceof TableSwitchInstruction
                || instruction instanceof LookupSwitchInstruction
                || (instruction instanceof BranchInstruction branch
                        && (branch.opcode() == Opcode.GOTO || branch.opcode() == Opcode.GOTO_W));
    }

    private static List<Label> whereItMayGo(Instruction instruction) {
        return switch (instruction) {
            case BranchInstruction it -> List.of(it.target());
            case TableSwitchInstruction it -> targetsOf(it.defaultTarget(),
                    it.cases().stream().map(SwitchCase::target).toList());
            case LookupSwitchInstruction it -> targetsOf(it.defaultTarget(),
                    it.cases().stream().map(SwitchCase::target).toList());
            default -> List.of();
        };
    }

    private static List<Label> targetsOf(Label otherwise, List<Label> cases) {
        List<Label> out = new ArrayList<>(cases);
        out.add(otherwise);
        return out;
    }
}
