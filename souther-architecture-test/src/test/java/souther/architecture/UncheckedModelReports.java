package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.TypeKind;
import java.lang.classfile.instruction.ArrayLoadInstruction;
import java.lang.classfile.instruction.ArrayStoreInstruction;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.ConvertInstruction;
import java.lang.classfile.instruction.ExceptionCatch;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.NewPrimitiveArrayInstruction;
import java.lang.classfile.instruction.NewReferenceArrayInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.lang.classfile.instruction.StoreInstruction;
import java.lang.classfile.instruction.SwitchCase;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * The methods of some test classes that read the report of a model without having asked that
 * that model compiles.
 *
 * <p>A model is a value, and what a method asked of it is asked of that value: a model made from
 * a source and then replaced by another is a model not asked about, and so is one of two models
 * when only the other was. So the walk follows each model through the local variable that holds
 * it, from where it was made to where its report is read. A model is asked about by handing it
 * to the helper, which stops the test on an error or compares the errors with the ones meant. What
 * matters is that the test cannot pass without the model having been asked about, so the call
 * stands before the read on every way to it, or after it on every way out of the method: a call
 * that a branch can step over, or a return that comes before it, does not count. That lets a
 * test read what a model has computed before anything was answered, and still be held to the
 * model compiling. A look at {@code errors()} is not a look, because nothing says what was done
 * with what it showed; the tests that mean a model not to compile say so to the helper.
 *
 * <p>A method that makes a model and returns it unasked hands the question to its callers, and a
 * method that reads, or asks about, the model it was handed passes that on to whoever handed it,
 * so a model made in one method and read in another is followed as well. A model that comes from
 * a field or from another class is asked about where it was made, and this does not see it. What
 * the walk cannot follow at all, a model that reaches a read through a branch or an operation
 * that is not a plain load, is counted by {@link #unresolved}, so that it is a thing to change in
 * the test and not a place the check is blind to.
 */
final class UncheckedModelReports {

    private static final String COMPILATION = "souther/compiler/query/Compilation";

    private static final String COMPILATION_TYPE = "L" + COMPILATION + ";";

    private static final String REPORT = "souther/compiler/report/AdequacyReport";

    private final String helper;

    /** @param helper the class a test goes through to ask that a model compiles */
    UncheckedModelReports(String helper) {
        this.helper = helper;
    }

    /** The refused methods of {@code classes}, as {@link AMethod} says them. */
    Set<String> in(Collection<ClassModel> classes) {
        Set<String> refused = new TreeSet<>();
        for (ClassModel each : classes) {
            for (Map.Entry<MethodModel, Walked> method : walked(each).entrySet()) {
                if (method.getValue().unasked > 0) {
                    refused.add(AMethod.of(each, method.getKey()));
                }
            }
        }
        return refused;
    }

    /** How many methods of {@code classes} make a model, ask about it, and then read its report. */
    int asking(Collection<ClassModel> classes) {
        int asked = 0;
        for (ClassModel each : classes) {
            for (Walked method : walked(each).values()) {
                if (method.asked > 0) {
                    asked++;
                }
            }
        }
        return asked;
    }

    /** The methods of {@code classes} that read a report of a model the walk cannot follow. */
    Set<String> unresolved(Collection<ClassModel> classes) {
        Set<String> lost = new TreeSet<>();
        for (ClassModel each : classes) {
            for (Map.Entry<MethodModel, Walked> method : walked(each).entrySet()) {
                if (method.getValue().lost > 0) {
                    lost.add(AMethod.of(each, method.getKey()));
                }
            }
        }
        return lost;
    }

    /**
     * What each method of {@code each} does, once what its callers and callees do to a model is
     * known. That is a fact about the class and is found by going round until it stops changing:
     * what a method returns made and unasked, what it reads of the model it is handed, and what it
     * asks of it, each depend on the same three of the methods it calls.
     */
    private Map<MethodModel, Walked> walked(ClassModel each) {
        Map<MethodModel, Walk> walks = new LinkedHashMap<>();
        for (MethodModel method : each.methods()) {
            if (method.code().isPresent()) {
                walks.put(method, new Walk(each, method));
            }
        }
        Facts facts = new Facts(Set.of(), Set.of(), Set.of());
        Map<MethodModel, Walked> walked = new LinkedHashMap<>();
        for (int round = 0; round < 12; round++) {
            walked.clear();
            Set<String> unasked = new HashSet<>();
            Set<String> readers = new HashSet<>();
            Set<String> askers = new HashSet<>();
            for (Map.Entry<MethodModel, Walk> walk : walks.entrySet()) {
                Walked one = walk.getValue().run(facts);
                walked.put(walk.getKey(), one);
                String key = key(walk.getKey());
                if (one.returnsUnasked) {
                    unasked.add(key);
                }
                one.readsParameters.forEach(index -> readers.add(key + "#" + index));
                one.asksParameters.forEach(index -> askers.add(key + "#" + index));
            }
            Facts next = new Facts(unasked, readers, askers);
            if (next.equals(facts)) {
                break;
            }
            facts = next;
        }
        return walked;
    }

    private static String key(MethodModel method) {
        return method.methodName().stringValue() + method.methodTypeSymbol().descriptorString();
    }

    private static String key(InvokeInstruction call) {
        return call.name().stringValue() + call.type().stringValue();
    }

    /** What the methods of one class are known to do with a model, by name and descriptor. */
    private record Facts(Set<String> returningUnasked, Set<String> readingParameter,
                         Set<String> askingParameter) { }

    /** What one method does with the models it meets. */
    private static final class Walked {
        /** Reads of a model that was made here, or came from a call, and never asked about. */
        int unasked;
        /** Reads of a model that was made here and asked about first. */
        int asked;
        /** Reads of a model the walk lost the way to. */
        int lost;
        boolean returnsUnasked;
        final Set<Integer> readsParameters = new HashSet<>();
        final Set<Integer> asksParameters = new HashSet<>();
    }

    /** Where a model stands where it is read. */
    private enum Standing { UNASKED, ASKED_HERE, ASKED, HANDED_IN, LOST }

    /** What holds a model on the stack: a local variable, the answer of a call, or something else. */
    private sealed interface Operand {
        record Local(int slot) implements Operand { }

        record Answer(InvokeInstruction call, int at) implements Operand { }

        record HandedIn() implements Operand { }

        record Lost() implements Operand { }
    }

    /** What a local variable holds: how the model it was given stands, and where it was stored. */
    private record Held(Standing made, int storedAt) { }

    /** A call at {@code at} that reads a report of {@code operand}, or asks about it. */
    private record Event(int at, boolean reads, Operand operand) { }

    /** The code of one method, as the instructions and the places a branch can land. */
    private final class Walk {

        private final ClassModel owner;
        private final MethodModel method;
        private final List<CodeElement> flow = new ArrayList<>();
        private final List<int[]> branches = new ArrayList<>();
        private final Map<Integer, Integer> parameterAt = new HashMap<>();
        private final Map<Integer, List<Integer>> asks = new HashMap<>();
        private final Map<Integer, List<Integer>> stores = new HashMap<>();
        private Facts facts;

        Walk(ClassModel owner, MethodModel method) {
            this.owner = owner;
            this.method = method;
            List<CodeElement> elements = method.code().orElseThrow().elementList();
            Set<Label> landings = new HashSet<>();
            for (CodeElement element : elements) {
                switch (element) {
                    case BranchInstruction branch -> landings.add(branch.target());
                    case LookupSwitchInstruction table -> {
                        landings.add(table.defaultTarget());
                        table.cases().forEach(each -> landings.add(each.target()));
                    }
                    case TableSwitchInstruction table -> {
                        landings.add(table.defaultTarget());
                        table.cases().forEach(each -> landings.add(each.target()));
                    }
                    case ExceptionCatch catching -> landings.add(catching.handler());
                    default -> { }
                }
            }
            Map<Label, Integer> landedAt = new HashMap<>();
            Map<Integer, List<Label>> jumps = new HashMap<>();
            for (CodeElement element : elements) {
                if (element instanceof LabelTarget at && landings.contains(at.label())) {
                    landedAt.put(at.label(), flow.size());
                    flow.add(element);
                } else if (element instanceof Instruction) {
                    jumps.put(flow.size(), targetsOf(element));
                    flow.add(element);
                }
            }
            jumps.forEach((from, labels) -> labels.forEach(
                    label -> branches.add(new int[] {from, landedAt.getOrDefault(label, -1)})));
            int slot = method.flags().has(AccessFlag.STATIC) ? 0 : 1;
            int index = 0;
            for (ClassDesc parameter : method.methodTypeSymbol().parameterList()) {
                parameterAt.put(slot, index++);
                slot += sizeOf(parameter);
            }
        }

        private static List<Label> targetsOf(CodeElement element) {
            List<Label> targets = new ArrayList<>();
            switch (element) {
                case BranchInstruction branch -> targets.add(branch.target());
                case LookupSwitchInstruction table -> {
                    targets.add(table.defaultTarget());
                    table.cases().stream().map(SwitchCase::target).forEach(targets::add);
                }
                case TableSwitchInstruction table -> {
                    targets.add(table.defaultTarget());
                    table.cases().stream().map(SwitchCase::target).forEach(targets::add);
                }
                default -> { }
            }
            return targets;
        }

        Walked run(Facts known) {
            this.facts = known;
            Map<Integer, List<Event>> events = new HashMap<>();
            asks.clear();
            stores.clear();
            for (int at = 0; at < flow.size(); at++) {
                CodeElement element = flow.get(at);
                if (element instanceof InvokeInstruction call) {
                    for (Event event : meet(call, at)) {
                        events.computeIfAbsent(at, k -> new ArrayList<>()).add(event);
                        if (!event.reads() && event.operand() instanceof Operand.Local local) {
                            asks.computeIfAbsent(local.slot(), k -> new ArrayList<>()).add(at);
                        }
                    }
                } else if (element instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE) {
                    stores.computeIfAbsent(store.slot(), k -> new ArrayList<>()).add(at);
                }
            }
            Walked walked = new Walked();
            Map<Integer, Held> held = new HashMap<>();
            boolean returnsModel = method.methodTypeSymbol().returnType().descriptorString()
                    .equals(COMPILATION_TYPE);
            for (int at = 0; at < flow.size(); at++) {
                CodeElement element = flow.get(at);
                if (element instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE) {
                    Standing standing = standing(producer(at, 0), held, at);
                    held.put(store.slot(), new Held(
                            standing == Standing.ASKED_HERE ? Standing.ASKED : standing, at));
                } else if (element instanceof InvokeInstruction) {
                    for (Event event : events.getOrDefault(at, List.of())) {
                        if (event.reads()) {
                            read(event.operand(), held, at, walked);
                        } else if (event.operand() instanceof Operand.Local local
                                && parameterAt.containsKey(local.slot())
                                && !held.containsKey(local.slot())) {
                            walked.asksParameters.add(parameterAt.get(local.slot()));
                        }
                    }
                } else if (returnsModel && element instanceof ReturnInstruction back
                        && back.typeKind() == TypeKind.REFERENCE
                        && standing(producer(at, 0), held, at) == Standing.UNASKED) {
                    walked.returnsUnasked = true;
                }
            }
            return walked;
        }

        /** The reads and the asks a call makes, of the models it is given. */
        private List<Event> meet(InvokeInstruction call, int at) {
            List<Event> events = new ArrayList<>();
            boolean ours = call.owner().asInternalName().equals(owner.thisClass().asInternalName());
            List<ClassDesc> parameters = new ArrayList<>(call.typeSymbol().parameterList());
            if (call.opcode() != Opcode.INVOKESTATIC) {
                parameters.add(0, call.owner().asSymbol());
            }
            int above = 0;
            for (int i = parameters.size() - 1; i >= 0; i--) {
                ClassDesc parameter = parameters.get(i);
                int index = call.opcode() == Opcode.INVOKESTATIC ? i : i - 1;
                above += sizeOf(parameter);
                if (!parameter.descriptorString().equals(COMPILATION_TYPE)) {
                    continue;
                }
                boolean receiver = index < 0;
                String site = key(call) + "#" + index;
                boolean reads = receiver ? readsReceiver(call)
                        : readsArgument(call) || (ours && facts.readingParameter().contains(site));
                boolean asks = !receiver && (call.owner().asInternalName().equals(helper)
                        || (ours && facts.askingParameter().contains(site)));
                if (reads || asks) {
                    events.add(new Event(at, reads, producer(at, above - sizeOf(parameter))));
                }
            }
            return events;
        }

        private boolean readsReceiver(InvokeInstruction call) {
            return call.owner().asInternalName().equals(COMPILATION)
                    && Set.of("db", "adequacy").contains(call.name().stringValue());
        }

        private boolean readsArgument(InvokeInstruction call) {
            return call.owner().asInternalName().equals(REPORT)
                    && call.name().stringValue().equals("of");
        }

        private void read(Operand operand, Map<Integer, Held> held, int at, Walked walked) {
            switch (standing(operand, held, at)) {
                case UNASKED -> walked.unasked++;
                case ASKED_HERE -> walked.asked++;
                case LOST -> walked.lost++;
                case HANDED_IN -> {
                    if (operand instanceof Operand.Local local
                            && parameterAt.containsKey(local.slot())) {
                        walked.readsParameters.add(parameterAt.get(local.slot()));
                    }
                }
                case ASKED -> { }
            }
        }

        private Standing standing(Operand operand, Map<Integer, Held> held, int at) {
            return switch (operand) {
                case Operand.Lost _ -> Standing.LOST;
                case Operand.HandedIn _ -> Standing.HANDED_IN;
                case Operand.Answer answer -> answered(answer, held, at);
                case Operand.Local local -> {
                    Held now = held.get(local.slot());
                    Standing made = now == null ? Standing.HANDED_IN : now.made();
                    int storedAt = now == null ? -1 : now.storedAt();
                    boolean asked = asks.getOrDefault(local.slot(), List.of()).stream()
                            .anyMatch(look -> counts(look, at, local.slot(), storedAt));
                    yield switch (made) {
                        case UNASKED -> asked ? Standing.ASKED_HERE : Standing.UNASKED;
                        case HANDED_IN -> asked ? Standing.ASKED : Standing.HANDED_IN;
                        default -> made;
                    };
                }
            };
        }

        /**
         * How the model a call answered stands. A model made by a factory is not asked about; one
         * a model answers for itself, to carry a day or a policy, is the same model and stands as
         * the one it came from.
         */
        private Standing answered(Operand.Answer answer, Map<Integer, Held> held, int at) {
            InvokeInstruction call = answer.call();
            String type = call.typeSymbol().returnType().descriptorString();
            if (!type.equals(COMPILATION_TYPE)) {
                return Standing.HANDED_IN;
            }
            String callee = call.owner().asInternalName();
            if (callee.equals(COMPILATION) && call.name().stringValue().startsWith("of")) {
                return Standing.UNASKED;
            }
            if (callee.equals(COMPILATION) && call.opcode() != Opcode.INVOKESTATIC) {
                int arguments = 0;
                for (ClassDesc parameter : call.typeSymbol().parameterList()) {
                    arguments += sizeOf(parameter);
                }
                return standing(producer(answer.at(), arguments), held, at);
            }
            if (callee.equals(helper)) {
                return Standing.ASKED;
            }
            if (callee.equals(owner.thisClass().asInternalName())
                    && facts.returningUnasked().contains(key(call))) {
                return Standing.UNASKED;
            }
            return Standing.HANDED_IN;
        }

        /**
         * Whether the look at {@code look} is one the read at {@code at} cannot go without. A look
         * before the read is, unless a branch can step over it on the way. A look after the read
         * is as well, unless the method can return, or a branch can step over the look, once the
         * read is done, or the variable is given another model before it.
         */
        private boolean counts(int look, int at, int slot, int storedAt) {
            if (look < at) {
                return storedAt < look && !steppedOver(look, at);
            }
            if (look == at) {
                return false;
            }
            for (int i = at + 1; i < look; i++) {
                if (flow.get(i) instanceof ReturnInstruction) {
                    return false;
                }
            }
            for (int[] branch : branches) {
                if (branch[0] >= at && branch[0] < look && branch[1] > look) {
                    return false;
                }
            }
            return stores.getOrDefault(slot, List.of()).stream()
                    .noneMatch(store -> store > at && store < look);
        }

        /** Whether a branch before {@code look} can land between it and {@code at}. */
        private boolean steppedOver(int look, int at) {
            for (int[] branch : branches) {
                if (branch[0] < look && branch[1] > look && branch[1] <= at) {
                    return true;
                }
            }
            return false;
        }

        /**
         * What put the value {@code above} slots below the top of the stack there, before the
         * instruction at {@code at}. Instructions that move a value without being its source are
         * stepped back over, and what cannot be placed is lost.
         */
        private Operand producer(int at, int above) {
            int need = above + 1;
            for (int i = at - 1; i >= 0; i--) {
                if (!(flow.get(i) instanceof Instruction instruction)) {
                    return new Operand.Lost();
                }
                if (instruction instanceof TypeCheckInstruction check
                        && check.opcode() == Opcode.CHECKCAST) {
                    continue;
                }
                int[] effect = effect(instruction);
                if (effect == null) {
                    return new Operand.Lost();
                }
                if (need <= effect[1]) {
                    return switch (instruction) {
                        case LoadInstruction load when load.typeKind() == TypeKind.REFERENCE ->
                                new Operand.Local(load.slot());
                        case InvokeInstruction call -> new Operand.Answer(call, i);
                        case FieldInstruction _ -> new Operand.HandedIn();
                        default -> new Operand.Lost();
                    };
                }
                need = need - effect[1] + effect[0];
            }
            return new Operand.Lost();
        }
    }

    /** What an instruction takes off the stack and what it puts on, or null where not known. */
    private static int[] effect(Instruction instruction) {
        return switch (instruction) {
            case LoadInstruction load -> new int[] {0, load.typeKind().slotSize()};
            case StoreInstruction store -> new int[] {store.typeKind().slotSize(), 0};
            case ConstantInstruction constant -> new int[] {0, constant.typeKind().slotSize()};
            case InvokeInstruction call -> shape(call.typeSymbol(),
                    call.opcode() == Opcode.INVOKESTATIC ? 0 : 1);
            case InvokeDynamicInstruction call -> shape(call.typeSymbol(), 0);
            case FieldInstruction field -> {
                int size = sizeOf(field.typeSymbol());
                yield switch (field.opcode()) {
                    case GETSTATIC -> new int[] {0, size};
                    case PUTSTATIC -> new int[] {size, 0};
                    case GETFIELD -> new int[] {1, size};
                    default -> new int[] {1 + size, 0};
                };
            }
            case NewObjectInstruction _ -> new int[] {0, 1};
            case NewReferenceArrayInstruction _ -> new int[] {1, 1};
            case NewPrimitiveArrayInstruction _ -> new int[] {1, 1};
            case ArrayLoadInstruction load -> new int[] {2, load.typeKind().slotSize()};
            case ArrayStoreInstruction store -> new int[] {2 + store.typeKind().slotSize(), 0};
            case ConvertInstruction convert ->
                    new int[] {convert.fromType().slotSize(), convert.toType().slotSize()};
            case TypeCheckInstruction _ -> new int[] {1, 1};
            case StackInstruction stack -> switch (stack.opcode()) {
                case POP -> new int[] {1, 0};
                case POP2 -> new int[] {2, 0};
                case DUP -> new int[] {1, 2};
                default -> null;
            };
            default -> null;
        };
    }

    private static int[] shape(MethodTypeDesc type, int receiver) {
        int arguments = receiver;
        for (ClassDesc parameter : type.parameterList()) {
            arguments += sizeOf(parameter);
        }
        return new int[] {arguments, sizeOf(type.returnType())};
    }

    private static int sizeOf(ClassDesc type) {
        return switch (type.descriptorString()) {
            case "V" -> 0;
            case "J", "D" -> 2;
            default -> 1;
        };
    }
}
