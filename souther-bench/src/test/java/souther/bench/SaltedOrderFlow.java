package souther.bench;

import souther.bench.SaltedOrder.Finding;
import souther.bench.SaltedOrder.Kind;
import souther.bench.SaltedOrder.Reading;
import souther.bench.SaltedOrder.Tag;
import souther.bench.SaltedOrder.Val;
import souther.bench.SaltedOrderVocabulary.Call;
import souther.bench.SaltedOrderVocabulary.Feed;
import souther.bench.SaltedOrderVocabulary.Outcome;
import souther.bench.SaltedOrderVocabulary.Push;
import souther.bench.SaltedOrderVocabulary.Signature;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.Label;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.TypeKind;
import java.lang.classfile.attribute.CodeAttribute;
import java.lang.classfile.instruction.ArrayLoadInstruction;
import java.lang.classfile.instruction.ArrayStoreInstruction;
import java.lang.classfile.instruction.BranchInstruction;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.ConvertInstruction;
import java.lang.classfile.instruction.ExceptionCatch;
import java.lang.classfile.instruction.FieldInstruction;
import java.lang.classfile.instruction.IncrementInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LabelTarget;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.LookupSwitchInstruction;
import java.lang.classfile.instruction.MonitorInstruction;
import java.lang.classfile.instruction.NewMultiArrayInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.NewPrimitiveArrayInstruction;
import java.lang.classfile.instruction.NewReferenceArrayInstruction;
import java.lang.classfile.instruction.OperatorInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.StackInstruction;
import java.lang.classfile.instruction.StoreInstruction;
import java.lang.classfile.instruction.SwitchCase;
import java.lang.classfile.instruction.TableSwitchInstruction;
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Predicate;

/**
 * Follows what comes out of an unordered copy, through every method of some classes, until it is
 * put in an order, asked something an order does not change, or becomes an answer.
 *
 * <p>An abstract interpretation of the bytecode, kept as small as the question lets it be. A value
 * is the set of things it is derived from — {@link SaltedOrder.Tag} — and nothing about what it is
 * otherwise: a number added up from the elements of a walk is not one, because a sum does not
 * depend on the order it was added in, and a comparison or a branch on one is not followed at all.
 *
 * <p><b>What it does not see.</b> A reader that returns one constant for the first of them to
 * match and another for the next kind chooses by position through control flow alone. So does one
 * that leaves the last element it met in a variable. A number made of an element is not followed
 * either: a sum is the same in any order, and a number left standing where two collide is not told
 * from it. The element a walk
 * is at belongs to the method that is walking: it is not handed to what that method calls, and it
 * is let go where the loop ends, because what a loop leaves behind is a fold of all the elements
 * as often as it is the last of them and the bytecode does not say which. An object made of one
 * ({@code new Word(each)}) is not followed either. Put in a list inside the walk it makes a list
 * in the walk's order, and that is not seen; following every object made of an element into every
 * list would read a list built by a loop over something else as though it had been built in the
 * order of the set the objects were made from. What is followed is what a walk makes of the
 * elements itself — a list, a text, an array, the first one a stream reaches, the one at an
 * index — which is where an order becomes an answer.
 *
 * <p><b>Where many elements meet in one place, the order says which is left.</b> The element a walk
 * is at becomes an answer when it leaves the walk by being returned or stored, unless the method
 * asked whether there is exactly one. A value put under a key is left holding the last, or the
 * first, unless the key is the element itself; a merge is as good as the function it is given, and
 * only the declared commutative ones are good; a collector that groups lists what it groups. A
 * sort ties what its comparator does not separate, so only the natural order, or a chain ending in
 * it, is total. A crossing puts the elements in an order and does not change which of several was
 * left standing. And an object taken out of a map is the one the map holds, so a list filled there
 * is filled in the map, when it is cast to something that holds a plurality.
 *
 * <p><b>A call is read where it is made.</b> What a method is handed by a call that hands it
 * something from a copy is read as that call's own, so a helper used from two places does not
 * answer for both, and a wrapper every module uses does not carry everything anyone put in it. A
 * call that hands nothing from a copy reads the method as it is with nothing handed. What a value
 * may be is narrowed by where it is held: a field typed as a text does not hold a set.
 *
 * <p><b>Fields are joined across the whole program.</b> What a field may hold is everything any
 * method wrote in it, since which object it is a field of is not followed. Only a field of a class
 * the reading begins in holds a value that came out of a copy, and not one that holds anything: a
 * plurality handed to any other field is where it leaves what is read, and is reported as having
 * left; an answer handed there is reported, since nothing after it is read.
 */
final class SaltedOrderFlow {

    private record MethodKey(String owner, String name, String descriptor) {

        @Override
        public String toString() {
            return owner.replace('/', '.') + "#" + name + descriptor;
        }
    }

    /** A method read in the context of one call: the call site that handed it what it holds. */
    private record Unit(MethodKey method, String context) {

        @Override
        public String toString() {
            return context.isEmpty() ? method.toString() : method + "@" + context;
        }
    }

    private final Map<MethodKey, MethodModel> methods = new LinkedHashMap<>();
    private final Map<String, Set<String>> supers = new HashMap<>();
    private final Map<String, Set<String>> subs = new HashMap<>();
    private final Set<String> called = new HashSet<>();
    private final Set<MethodKey> asksForExactlyOne = new HashSet<>();
    private final Predicate<String> beginsAt;

    private final Map<String, Set<Tag>> facts = new HashMap<>();
    private final Map<String, Set<Unit>> readers = new HashMap<>();
    private final Map<String, Set<String>> fieldsOf = new HashMap<>();
    private final Map<MethodKey, List<MethodKey>> runs = new HashMap<>();
    private final Map<String, Integer> captured = new HashMap<>();
    private final Deque<Unit> queue = new ArrayDeque<>();
    private final Set<Unit> queued = new HashSet<>();
    private final Set<Unit> started = new HashSet<>();
    private final Map<MethodKey, Val> handsOutAnAnswer = new LinkedHashMap<>();

    private final Set<String> roots = new LinkedHashSet<>();
    private final Map<Reported, Set<String>> findings = new LinkedHashMap<>();
    private final Map<String, Set<String>> reached = new LinkedHashMap<>();

    /** One thing that was found, of one reader. */
    private record Reported(String reader, String what) {}

    private SaltedOrderFlow(List<ClassModel> universe, Predicate<String> beginsAt) {
        this.beginsAt = beginsAt;
        for (ClassModel model : universe) {
            String name = model.thisClass().asInternalName();
            Set<String> above = new LinkedHashSet<>();
            model.superclass().ifPresent(each -> above.add(each.asInternalName()));
            model.interfaces().forEach(each -> above.add(each.asInternalName()));
            supers.put(name, above);
            for (String up : above) {
                subs.computeIfAbsent(up, k -> new LinkedHashSet<>()).add(name);
            }
            for (MethodModel method : model.methods()) {
                methods.put(new MethodKey(name, method.methodName().stringValue(),
                        method.methodType().stringValue()), method);
            }
        }
        for (ClassModel model : universe) {
            for (MethodModel method : model.methods()) {
                MethodKey in = new MethodKey(model.thisClass().asInternalName(),
                        method.methodName().stringValue(), method.methodType().stringValue());
                method.code().ifPresent(code -> {
                    for (CodeElement each : code) {
                        if (each instanceof InvokeInstruction call) {
                            called.add(call.name().stringValue() + call.type().stringValue());
                        } else if (each instanceof InvokeDynamicInstruction dynamic) {
                            for (var argument : dynamic.bootstrapArgs()) {
                                if (argument instanceof DirectMethodHandleDesc handle) {
                                    called.add(handle.methodName() + handle.lookupDescriptor());
                                }
                            }
                        }
                    }
                    if (comparesASizeWithOne(code.elementList())) {
                        asksForExactlyOne.add(in);
                    }
                });
            }
        }
    }

    /**
     * Whether a method asks if there is exactly one of something.
     *
     * <p>A method that does takes the first of it and means the only one, and the bytecode of the
     * first of one reads the same as the first of many. So a method that asks is not read as
     * choosing among them by where they stand.
     */
    private static boolean comparesASizeWithOne(List<CodeElement> elements) {
        for (int at = 0; at < elements.size(); at++) {
            if (!(elements.get(at) instanceof InvokeInstruction call)
                    || !call.name().stringValue().equals("size")) {
                continue;
            }
            int seen = 0;
            boolean one = false;
            for (int after = at + 1; after < elements.size() && seen < 3; after++) {
                CodeElement next = elements.get(after);
                if (!(next instanceof Instruction)) {
                    continue;
                }
                seen++;
                if (next instanceof ConstantInstruction constant
                        && Integer.valueOf(1).equals(constant.constantValue())) {
                    one = true;
                } else if (next instanceof BranchInstruction branch && one
                        && (branch.opcode() == Opcode.IF_ICMPEQ
                                || branch.opcode() == Opcode.IF_ICMPNE)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Reads every method of {@code universe}, starting from each copy in a class {@code beginsAt}
     * accepts.
     */
    static Reading read(List<ClassModel> universe, Predicate<String> beginsAt) {
        SaltedOrderFlow flow = new SaltedOrderFlow(universe, beginsAt);
        flow.run();
        return flow.finish();
    }

    private void run() {
        for (var each : methods.entrySet()) {
            if (each.getValue().code().isPresent()) {
                enqueueOnce(new Unit(each.getKey(), ""));
            }
        }
        int reads = 0;
        int most = methods.size() * 60;
        while (!queue.isEmpty()) {
            Unit next = queue.poll();
            queued.remove(next);
            analyse(next);
            if (++reads > most) {
                throw new AssertionError("the reading does not settle: " + reads + " reads of "
                        + methods.size() + " methods, and " + queue.size() + " still waiting");
            }
        }
    }

    private void enqueue(Unit unit) {
        if (queued.add(unit)) {
            queue.add(unit);
        }
    }

    /** A method read for the first time in a context; after that only what it reads changing does. */
    private void enqueueOnce(Unit unit) {
        if (started.add(unit)) {
            enqueue(unit);
        }
    }

    private Reading finish() {
        for (var each : handsOutAnAnswer.entrySet()) {
            MethodKey method = each.getKey();
            String signature = method.name() + method.descriptor();
            // What every object answers, and is asked by whatever prints or compares it, so that
            // there is always a caller and none of them is in the program.
            boolean everyObjectAnswersIt = Set.of("toString", "hashCode", "equals")
                    .contains(method.name());
            if (!called.contains(signature) && !method.name().startsWith("lambda$")
                    && !everyObjectAnswersIt) {
                note(method.toString(), "returns an order the run gave to a caller that is not"
                        + " there, made at " + sitesOf(each.getValue()), each.getValue().origins());
            }
        }
        List<Finding> out = new ArrayList<>();
        for (var each : findings.entrySet()) {
            out.add(new Finding(each.getKey().reader(), each.getKey().what(), each.getValue()));
        }
        return new Reading(roots, out, reached);
    }

    private static Set<String> originsOf(Set<Tag> tags) {
        Set<String> out = new LinkedHashSet<>();
        for (Tag each : tags) {
            if (each.cameOutOfACopy()) {
                out.add(each.origin());
            }
        }
        return out;
    }

    private void note(String reader, String what, Set<String> origins) {
        findings.computeIfAbsent(new Reported(reader, what), k -> new TreeSet<>())
                .addAll(origins);
    }

    /** These tags, each made an answer at {@code where} if it is one and was not already. */
    private static Set<Tag> madeAt(Set<Tag> tags, String where) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : tags) {
            out.add(each.madeAt(where));
        }
        return out;
    }

    private static Set<String> sitesOf(Val value) {
        Set<String> sites = new TreeSet<>();
        for (Tag each : value.tags()) {
            if (each.isAnAnswer()) {
                sites.add(each.site());
            }
        }
        return sites;
    }

    private void reach(Set<String> origins, String how) {
        for (String origin : origins) {
            reached.computeIfAbsent(origin, k -> new LinkedHashSet<>()).add(how);
        }
    }

    // ---- facts

    private Set<Tag> readFact(String key, Unit by) {
        readers.computeIfAbsent(key, k -> new HashSet<>()).add(by);
        return facts.getOrDefault(key, Set.of());
    }

    /**
     * What a field, a parameter or a return may hold from now on.
     *
     * <p>Only what came out of a copy is carried between methods. A function, or a collector, lives
     * as long as the method that made it and hands what it is given on where it is called: carried
     * across every call, each lambda of the program would be a fact of its own.
     */
    private void joinFact(String key, Set<Tag> given) {
        Set<Tag> tags = new LinkedHashSet<>();
        for (Tag each : given) {
            if (each.cameOutOfACopy()) {
                tags.add(each);
            }
        }
        if (tags.isEmpty()) {
            return;
        }
        Set<Tag> held = facts.computeIfAbsent(key, k -> new LinkedHashSet<>());
        if (held.addAll(tags)) {
            for (Unit each : readers.getOrDefault(key, Set.of())) {
                enqueue(each);
            }
            if (key.startsWith("F:")) {
                String owner = key.substring(2, key.lastIndexOf('.'));
                fieldsOf.computeIfAbsent(owner, k -> new LinkedHashSet<>()).add(key);
                for (Unit each : readers.getOrDefault("C:" + owner, Set.of())) {
                    enqueue(each);
                }
            }
        }
    }

    private static String fieldKey(String owner, String name) {
        return "F:" + owner + "." + name;
    }

    // ---- what a place may hold

    /** Types that can be anything, so that what is held there may be a plurality. */
    private static final Set<String> HOLDS_ANYTHING = Set.of(
            "java/lang/Object", "java/lang/Comparable", "java/io/Serializable",
            "java/lang/Cloneable", "java/lang/Iterable");

    /** Whether a value of this kind can be held where a descriptor says. */
    private static boolean holds(Tag tag, String descriptor) {
        if (!tag.cameOutOfACopy()) {
            return true;
        }
        if (descriptor.length() == 1) {
            // A position, which is what indexOf answers, and nothing else a number is.
            return tag.isPositional() && (descriptor.equals("I") || descriptor.equals("J"));
        }
        if (descriptor.startsWith("[")) {
            return tag.isPositional();
        }
        String type = descriptor.substring(1, descriptor.length() - 1);
        if (HOLDS_ANYTHING.contains(type)) {
            return true;
        }
        if (type.equals("java/lang/String") || type.equals("java/lang/CharSequence")
                || type.equals("java/lang/StringBuilder")) {
            return tag.isPositional();
        }
        boolean aLibraryCollection = (type.startsWith("java/util/")
                && !type.startsWith("java/util/function/"))
                || type.startsWith("tools/jackson/databind/node/");
        if (aLibraryCollection || type.startsWith("java/util/stream/")) {
            return true;
        }
        return tag.kind() == Kind.PICKED || tag.kind() == Kind.CHOSEN;
    }

    private static Val narrowed(Val value, String descriptor) {
        if (value.isClean()) {
            return value;
        }
        Set<Tag> kept = new LinkedHashSet<>();
        for (Tag each : value.tags()) {
            if (holds(each, descriptor)) {
                kept.add(each);
            }
        }
        return kept.size() == value.tags().size() ? value : value.withTags(kept);
    }

    private static Set<Tag> narrowed(Set<Tag> tags, String descriptor) {
        return narrowed(Val.of(tags), descriptor).tags();
    }

    // ---- one method

    private static final class State {

        final Val[] locals;
        final List<Val> stack;

        State(Val[] locals, List<Val> stack) {
            this.locals = locals;
            this.stack = stack;
        }

        State copy() {
            return new State(locals.clone(), new ArrayList<>(stack));
        }

        State withoutElements() {
            Val[] kept = new Val[locals.length];
            for (int at = 0; at < locals.length; at++) {
                kept[at] = locals[at] == null ? null : locals[at].withoutElements();
            }
            List<Val> pending = new ArrayList<>();
            for (Val each : stack) {
                pending.add(each.withoutElements());
            }
            return new State(kept, pending);
        }

        boolean join(State other) {
            boolean changed = false;
            for (int at = 0; at < locals.length; at++) {
                Val mine = locals[at];
                Val theirs = other.locals[at];
                if (theirs == null) {
                    continue;
                }
                Val both = mine == null ? theirs : mine.join(theirs);
                changed |= mine == null || !both.equals(mine);
                locals[at] = both;
            }
            int shared = Math.min(stack.size(), other.stack.size());
            for (int at = 0; at < shared; at++) {
                Val mine = stack.get(at);
                Val both = mine.join(other.stack.get(at));
                if (!both.equals(mine)) {
                    changed = true;
                    stack.set(at, both);
                }
            }
            return changed;
        }

        Val pop() {
            return stack.remove(stack.size() - 1);
        }

        void push(Val value) {
            stack.add(value);
        }
    }

    private void analyse(Unit unit) {
        MethodKey key = unit.method();
        MethodModel method = methods.get(key);
        CodeModel code = method.code().orElse(null);
        if (code == null) {
            return;
        }
        List<CodeElement> elements = code.elementList();
        int size = elements.size();
        Map<Label, Integer> at = new HashMap<>();
        for (int index = 0; index < size; index++) {
            if (elements.get(index) instanceof LabelTarget target) {
                at.put(target.label(), index);
            }
        }
        List<int[]> handled = new ArrayList<>();
        for (ExceptionCatch each : code.exceptionHandlers()) {
            handled.add(new int[] {at.get(each.tryStart()), at.get(each.tryEnd()),
                    at.get(each.handler())});
        }
        int maxLocals = ((CodeAttribute) code).maxLocals();
        MethodTypeDesc type = MethodTypeDesc.ofDescriptor(key.descriptor());
        boolean isStatic = method.flags().has(AccessFlag.STATIC);
        Val[] seed = new Val[Math.max(maxLocals, 1)];
        int slot = 0;
        int index = 0;
        if (!isStatic) {
            seed[0] = seeded(unit, index++, "L0", false, "L" + key.owner() + ";");
            slot = 1;
        }
        for (ClassDesc each : type.parameterList()) {
            boolean wide = isWide(each);
            if (slot < seed.length) {
                seed[slot] = seeded(unit, index, "L" + slot, wide, each.descriptorString());
            }
            slot += wide ? 2 : 1;
            index++;
        }

        Set<Integer> exits = whereWalksEnd(elements, at);
        State[] in = new State[size + 1];
        in[0] = new State(seed, new ArrayList<>());
        BitSet pending = new BitSet();
        pending.set(0);
        while (!pending.isEmpty()) {
            int here = pending.nextSetBit(0);
            pending.clear(here);
            State state = in[here].copy();
            for (int[] range : handled) {
                if (here >= range[0] && here < range[1]) {
                    State caught = new State(state.locals.clone(),
                            new ArrayList<>(List.of(Val.CLEAN)));
                    merge(in, pending, range[2], caught);
                }
            }
            List<Integer> next = new ArrayList<>();
            step(unit, elements.get(here), here, state, at, next, isStatic, type,
                    seed.length);
            if (next.isEmpty() && continues(elements.get(here)) && here + 1 < size) {
                next.add(here + 1);
            }
            for (int to : next) {
                merge(in, pending, to, exits.contains(to) ? state.withoutElements() : state);
            }
        }
    }

    /**
     * Where each walk by hand ends: the place the test that asks whether there is another sends
     * control to when there is not.
     *
     * <p>An element is the walk's while the walk goes on. What is made of it inside the loop is
     * made of one element at a time, and what the loop leaves in a variable at the end is a fold of
     * all of them or the last of them, and which of those it is is not something a walk of the
     * bytecode can tell: so it is not taken for the order.
     */
    private static Set<Integer> whereWalksEnd(List<CodeElement> elements, Map<Label, Integer> at) {
        Set<Integer> exits = new HashSet<>();
        for (int index = 0; index < elements.size(); index++) {
            if (!(elements.get(index) instanceof InvokeInstruction call)) {
                continue;
            }
            String name = call.name().stringValue();
            if (!name.equals("hasNext") && !name.equals("hasMoreElements")) {
                continue;
            }
            for (int after = index + 1; after < elements.size(); after++) {
                CodeElement next = elements.get(after);
                if (next instanceof BranchInstruction branch) {
                    if (branch.opcode() == Opcode.IFEQ) {
                        exits.add(at.get(branch.target()));
                    }
                    break;
                }
                if (next instanceof Instruction) {
                    break;
                }
            }
        }
        return exits;
    }

    private Val seeded(Unit unit, int parameter, String home, boolean wide, String descriptor) {
        Set<Tag> tags = new LinkedHashSet<>();
        for (Tag each : narrowed(readFact("P:" + unit + "#" + parameter, unit), descriptor)) {
            // What a walk hands a method is the one element that call is made for.
            tags.add(each.handedToACall());
        }
        return new Val(tags, wide, -1, null, home);
    }

    private static void merge(State[] in, BitSet pending, int to, State state) {
        if (in[to] == null) {
            in[to] = state.copy();
            pending.set(to);
        } else if (in[to].join(state)) {
            pending.set(to);
        }
    }

    private static boolean continues(CodeElement element) {
        return !(element instanceof ReturnInstruction || element instanceof ThrowInstruction
                || element instanceof TableSwitchInstruction
                || element instanceof LookupSwitchInstruction
                || (element instanceof BranchInstruction branch
                        && (branch.opcode() == Opcode.GOTO || branch.opcode() == Opcode.GOTO_W)));
    }

    private static boolean isWide(ClassDesc type) {
        String text = type.descriptorString();
        return text.equals("J") || text.equals("D");
    }

    private static boolean isWide(TypeKind kind) {
        return kind == TypeKind.LONG || kind == TypeKind.DOUBLE;
    }

    /** One instruction: what it does to the state, and where control goes when it is not next. */
    private void step(Unit unit, CodeElement element, int index, State state,
                      Map<Label, Integer> at, List<Integer> next, boolean isStatic,
                      MethodTypeDesc type, int slots) {
        switch (element) {
            case LoadInstruction load -> {
                Val held = state.locals[load.slot()];
                Val value = held == null ? Val.clean(isWide(load.typeKind())) : held;
                state.push(value.withHome("L" + load.slot()).asWide(isWide(load.typeKind())));
            }
            case StoreInstruction store -> {
                Val value = state.pop();
                state.locals[store.slot()] = value.withHome(null);
                if (isWide(store.typeKind()) && store.slot() + 1 < state.locals.length) {
                    state.locals[store.slot() + 1] = null;
                }
            }
            case IncrementInstruction _ -> { }
            case ConstantInstruction constant -> state.push(Val.clean(isWide(constant.typeKind())));
            case ArrayLoadInstruction load -> {
                state.pop();
                Val array = state.pop();
                state.push(new Val(array.as(Kind.PICKED), isWide(load.typeKind()), -1, null, null));
            }
            case ArrayStoreInstruction _ -> {
                Val value = state.pop();
                state.pop();
                Val array = state.pop();
                Set<Tag> into = new LinkedHashSet<>();
                for (Tag each : value.tags()) {
                    if (each.isPositional()) {
                        into.add(new Tag(Kind.SEQUENCE, each.origin())
                                .madeAt(unit + ":" + index + " stores in an array"));
                    }
                }
                place(state, array, into);
            }
            case OperatorInstruction operator -> {
                boolean unary = operator.opcode() == Opcode.ARRAYLENGTH
                        || operator.opcode().name().endsWith("NEG");
                state.pop();
                if (!unary) {
                    state.pop();
                }
                boolean compares = operator.opcode().name().contains("CMP");
                state.push(Val.clean(isWide(operator.typeKind()) && !compares
                        && operator.opcode() != Opcode.ARRAYLENGTH));
            }
            case ConvertInstruction convert -> {
                state.pop();
                state.push(Val.clean(isWide(convert.toType())));
            }
            case StackInstruction stack -> stackOp(state, stack.opcode());
            case BranchInstruction branch -> {
                Opcode op = branch.opcode();
                boolean unconditional = op == Opcode.GOTO || op == Opcode.GOTO_W;
                if (!unconditional) {
                    state.pop();
                    if (op.name().startsWith("IF_")) {
                        state.pop();
                    }
                }
                next.add(at.get(branch.target()));
                if (!unconditional) {
                    next.add(index + 1);
                }
            }
            case TableSwitchInstruction table -> {
                state.pop();
                next.add(at.get(table.defaultTarget()));
                for (SwitchCase each : table.cases()) {
                    next.add(at.get(each.target()));
                }
            }
            case LookupSwitchInstruction lookup -> {
                state.pop();
                next.add(at.get(lookup.defaultTarget()));
                for (SwitchCase each : lookup.cases()) {
                    next.add(at.get(each.target()));
                }
            }
            case ReturnInstruction ret -> returned(unit, ret, state, isStatic, type, slots);
            case ThrowInstruction _ -> state.pop();
            case NewObjectInstruction made ->
                    state.push(Val.CLEAN.withAlloc(index + 1)
                            .withMade(made.className().asInternalName()));
            case NewPrimitiveArrayInstruction _ -> {
                state.pop();
                state.push(Val.CLEAN.withAlloc(index + 1).withMade("array"));
            }
            case NewReferenceArrayInstruction _ -> {
                state.pop();
                state.push(Val.CLEAN.withAlloc(index + 1).withMade("array"));
            }
            case NewMultiArrayInstruction multi -> {
                for (int each = 0; each < multi.dimensions(); each++) {
                    state.pop();
                }
                state.push(Val.CLEAN.withAlloc(index + 1).withMade("array"));
            }
            case TypeCheckInstruction check -> {
                if (check.opcode() == Opcode.INSTANCEOF) {
                    state.pop();
                    state.push(Val.CLEAN);
                } else {
                    Val value = state.pop();
                    String cast = check.type().asInternalName();
                    // What is taken out of a map is an object to fill only where it is cast to
                    // something that holds a plurality; cast to anything else it is a value.
                    if (value.isHeldInAMap() && !SaltedOrderVocabulary.inTheCollectionsLibrary(cast)) {
                        value = value.apartFromAnyPlace();
                    }
                    state.push(narrowed(value, cast.startsWith("[") ? cast : "L" + cast + ";"));
                }
            }
            case MonitorInstruction _ -> state.pop();
            case FieldInstruction field -> field(unit, field, state);
            case InvokeInstruction call -> invoke(unit, call, index, state);
            case InvokeDynamicInstruction dynamic -> dynamic(unit, dynamic, index, state);
            default -> { }
        }
    }

    private void returned(Unit unit, ReturnInstruction ret, State state, boolean isStatic,
                          MethodTypeDesc type, int slots) {
        if (ret.typeKind() != TypeKind.VOID) {
            Val value = narrowed(state.pop(), type.returnType().descriptorString());
            // What a function's body returns is handed back to the walk that runs it. Anything else
            // that returns the element a walk is at has taken the first, the last or any of them.
            if (!unit.method().name().startsWith("lambda$")) {
                // An element handed to this method is the one it was made for, and is what it hands
                // back; the walk is the caller's.
                value = value.leavingTheWalkAt(unit.method() + " returns an element a walk was at",
                        true);
            }
            joinFact("R:" + unit, value.tags());
            for (Tag each : value.tags()) {
                if (each.kind() == Kind.COLLECTION) {
                    reach(Set.of(each.origin()), "returned by " + unit.method());
                }
            }
            boolean readOffAField = value.home() != null && value.home().startsWith("F:");
            if (value.holdsAnAnswer() && !readOffAField) {
                handsOutAnAnswer.merge(unit.method(), value, Val::join);
            }
        }
        int slot = isStatic ? 0 : 1;
        if (!isStatic && state.locals[0] != null) {
            joinFact("O:" + unit + "#0", state.locals[0].tags());
        }
        int parameter = isStatic ? 0 : 1;
        for (ClassDesc each : type.parameterList()) {
            if (slot < slots && state.locals[slot] != null) {
                joinFact("O:" + unit + "#" + parameter, state.locals[slot].tags());
            }
            slot += isWide(each) ? 2 : 1;
            parameter++;
        }
    }

    private static void stackOp(State state, Opcode op) {
        switch (op) {
            case POP -> state.pop();
            case POP2 -> {
                if (!state.pop().wide()) {
                    state.pop();
                }
            }
            case DUP -> state.push(state.stack.get(state.stack.size() - 1));
            case DUP_X1 -> {
                Val one = state.pop();
                Val two = state.pop();
                state.push(one);
                state.push(two);
                state.push(one);
            }
            case DUP_X2 -> {
                Val one = state.pop();
                Val two = state.pop();
                if (two.wide()) {
                    state.push(one);
                    state.push(two);
                    state.push(one);
                } else {
                    Val three = state.pop();
                    state.push(one);
                    state.push(three);
                    state.push(two);
                    state.push(one);
                }
            }
            case DUP2 -> {
                Val one = state.pop();
                if (one.wide()) {
                    state.push(one);
                    state.push(one);
                } else {
                    Val two = state.pop();
                    state.push(two);
                    state.push(one);
                    state.push(two);
                    state.push(one);
                }
            }
            case DUP2_X1 -> {
                Val one = state.pop();
                if (one.wide()) {
                    Val two = state.pop();
                    state.push(one);
                    state.push(two);
                    state.push(one);
                } else {
                    Val two = state.pop();
                    Val three = state.pop();
                    state.push(two);
                    state.push(one);
                    state.push(three);
                    state.push(two);
                    state.push(one);
                }
            }
            case DUP2_X2 -> {
                Val one = state.pop();
                if (one.wide()) {
                    Val two = state.pop();
                    if (two.wide()) {
                        state.push(one);
                        state.push(two);
                        state.push(one);
                    } else {
                        Val three = state.pop();
                        state.push(one);
                        state.push(three);
                        state.push(two);
                        state.push(one);
                    }
                } else {
                    Val two = state.pop();
                    Val three = state.pop();
                    if (three.wide()) {
                        state.push(two);
                        state.push(one);
                        state.push(three);
                        state.push(two);
                        state.push(one);
                    } else {
                        Val four = state.pop();
                        state.push(two);
                        state.push(one);
                        state.push(four);
                        state.push(three);
                        state.push(two);
                        state.push(one);
                    }
                }
            }
            case SWAP -> {
                Val one = state.pop();
                Val two = state.pop();
                state.push(one);
                state.push(two);
            }
            default -> throw new AssertionError("a stack instruction this does not read: " + op);
        }
    }

    // ---- places

    private static boolean sameObject(Val held, Val target) {
        return (target.alloc() >= 0 && held.alloc() == target.alloc())
                || (target.home() != null && target.home().equals(held.home()));
    }

    /** Adds tags to every place the object {@code target} is held, and to the field it came from. */
    private void place(State state, Val target, Set<Tag> tags) {
        if (tags.isEmpty()) {
            return;
        }
        for (int at = 0; at < state.locals.length; at++) {
            Val held = state.locals[at];
            if (held != null && (sameObject(held, target)
                    || (target.home() != null && target.home().equals("L" + at)))) {
                state.locals[at] = held.plus(tags);
            }
        }
        for (int at = 0; at < state.stack.size(); at++) {
            Val held = state.stack.get(at);
            if (sameObject(held, target)) {
                state.stack.set(at, held.plus(tags));
            }
        }
        if (target.home() != null && target.home().startsWith("F:")) {
            joinFact(target.home(), tags);
        }
    }

    private static void clear(State state, Val target) {
        for (int at = 0; at < state.locals.length; at++) {
            Val held = state.locals[at];
            if (held != null && (sameObject(held, target)
                    || (target.home() != null && target.home().equals("L" + at)))) {
                state.locals[at] = held.withTags(Set.of());
            }
        }
        for (int at = 0; at < state.stack.size(); at++) {
            Val held = state.stack.get(at);
            if (sameObject(held, target)) {
                state.stack.set(at, held.withTags(Set.of()));
            }
        }
    }

    // ---- fields

    private void field(Unit unit, FieldInstruction field, State state) {
        String owner = field.owner().asInternalName();
        String name = field.name().stringValue();
        String fact = fieldKey(owner, name);
        ClassDesc type = field.typeSymbol();
        boolean wide = isWide(type);
        switch (field.opcode()) {
            case GETSTATIC, GETFIELD -> {
                Val receiver = field.opcode() == Opcode.GETFIELD ? state.pop() : Val.CLEAN;
                Set<Tag> tags = new LinkedHashSet<>(readFact(fact, unit));
                for (Tag each : receiver.tags()) {
                    if (each.kind() == Kind.PICKED || each.kind() == Kind.CHOSEN) {
                        tags.add(each);
                    }
                }
                state.push(new Val(narrowed(tags, type.descriptorString()), wide, -1, null, fact));
            }
            default -> {
                Val value = narrowed(state.pop(), type.descriptorString())
                        .leavingTheWalkAt(unit.method() + " stores an element a walk was at", false);
                if (field.opcode() == Opcode.PUTFIELD) {
                    state.pop();
                }
                boolean carriesIt = beginsAt.test(owner)
                        && !type.descriptorString().equals("Ljava/lang/Object;");
                Set<Tag> kept = new LinkedHashSet<>();
                for (Tag each : value.tags()) {
                    if (each.kind() == Kind.COLLECTION || each.kind() == Kind.TRAVERSAL
                            || (carriesIt && each.isAnAnswer())) {
                        kept.add(each);
                    }
                }
                if (value.holdsAnAnswer() && !carriesIt) {
                    note(unit.method().owner().replace('/', '.') + "#" + unit.method().name(),
                            "keeps in " + owner.replace('/', '.') + "." + name
                                    + " an order the run gave, made at " + sitesOf(value)
                                    + (unit.context().isEmpty() ? ""
                                            : ", handed what it keeps at " + unit.context()),
                            value.origins());
                }
                for (Tag each : kept) {
                    if (each.kind() == Kind.COLLECTION) {
                        reach(Set.of(each.origin()), (carriesIt ? "held in "
                                : "handed on to a field outside what is read: ")
                                + owner.replace('/', '.') + "." + name);
                    }
                }
                if (carriesIt) {
                    joinFact(fact, kept);
                }
            }
        }
    }

    // ---- calls

    private static boolean isJava(String owner) {
        return owner.startsWith("java/") || owner.startsWith("javax/") || owner.startsWith("jdk/");
    }

    /**
     * Whether a call is handed a plurality that came out of a copy, or an answer made of one.
     *
     * <p>The element a walk is at is not that. It stays in the method that is walking, and what a
     * callee makes of it comes back as what the call returns: carried into every method it is
     * handed to, an element would be read again as the walk's own wherever it went, including where
     * a method builds a text out of the parts of the one element it was given.
     */
    private static boolean carriesACopy(Val receiver, List<Val> args) {
        if (!withoutElements(receiver.tags()).isEmpty()) {
            return true;
        }
        for (Val each : args) {
            if (!withoutElements(each.tags()).isEmpty()) {
                return true;
            }
        }
        return false;
    }

    private static Set<Tag> withoutElements(Set<Tag> tags) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : tags) {
            if (each.cameOutOfACopy() && each.kind() != Kind.PICKED) {
                out.add(each);
            }
        }
        return out;
    }

    /** The elements a walk is at that a call was handed, which what it returns is made of. */
    private static Set<Tag> elementsIn(Val receiver, List<Val> args) {
        Set<Tag> out = new LinkedHashSet<>();
        for (Tag each : receiver.tags()) {
            if (each.kind() == Kind.PICKED) {
                out.add(each);
            }
        }
        for (Val value : args) {
            for (Tag each : value.tags()) {
                if (each.kind() == Kind.PICKED) {
                    out.add(each);
                }
            }
        }
        return out;
    }

    private void invoke(Unit unit, InvokeInstruction call, int index, State state) {
        MethodKey key = unit.method();
        String owner = call.owner().asInternalName();
        String name = call.name().stringValue();
        String descriptor = call.type().stringValue();
        MethodTypeDesc type = call.typeSymbol();
        boolean isStatic = call.opcode() == Opcode.INVOKESTATIC;
        int count = type.parameterCount();
        List<Val> args = new ArrayList<>();
        for (int each = 0; each < count; each++) {
            args.add(0, state.pop());
        }
        Val receiver = isStatic ? Val.CLEAN : state.pop();
        String returns = type.returnType().descriptorString();
        boolean returnsAValue = !returns.equals("V");
        boolean returnsAReference = returns.startsWith("L") || returns.startsWith("[");
        String where = key.owner().replace('/', '.') + "#" + key.name();

        Set<Tag> result = new LinkedHashSet<>();
        Val made = null;

        Signature signature = new Signature(owner, name, descriptor);
        if (isStatic && SaltedOrderVocabulary.declaredTotalOrders().contains(signature)) {
            state.push(Val.of(new Tag(Kind.TOTAL_ORDER, "")));
            return;
        }
        boolean crosses = SaltedOrderVocabulary.crosses(signature);
        if (crosses || SaltedOrderVocabulary.folds(signature)) {
            Set<Tag> given = new LinkedHashSet<>(receiver.tags());
            for (Val each : args) {
                given.addAll(each.tags());
            }
            reach(originsOf(given), (crosses ? "put in an order by " : "folded by ")
                    + signature.spelled());
            if (returnsAValue) {
                // What is put in an order is the elements. Which of several was left standing where
                // they met is not something an order among them changes.
                Set<Tag> left = new LinkedHashSet<>();
                for (Tag each : given) {
                    if (each.kind() == Kind.CHOSEN) {
                        left.add(each);
                    }
                }
                state.push(new Val(narrowed(left, returns), isWide(type.returnType()), -1, null,
                        null));
            }
            return;
        }
        if (isStatic && beginsAt.test(key.owner()) && isACopy(owner, name, count)) {
            String origin = key.owner().replace('/', '.') + "#" + key.name() + ":"
                    + owner.substring(owner.lastIndexOf('/') + 1) + "." + name + "@" + index;
            roots.add(origin);
            reached.computeIfAbsent(origin, k -> new LinkedHashSet<>());
            result.add(new Tag(Kind.COLLECTION, origin));
        }

        boolean tainted = carriesACopy(receiver, args);
        String context = tainted ? where + ":" + index : "";

        // A function is called on the value that stands for it.
        Set<Tag> functions = receiver.functions();
        boolean runsAFunction = !functions.isEmpty() && !isStatic && !isDerivingFunction(name);
        if (runsAFunction) {
            List<Set<Tag>> handed = new ArrayList<>();
            for (Val each : args) {
                handed.add(each.tags());
            }
            String ran = where + ":" + index + " " + owner.replace('/', '.') + "." + name;
            for (Tag function : functions) {
                result.addAll(function.origin().startsWith("ref|")
                        ? runLibraryRef(state, function.origin(), handed, where, ran)
                        : callFunction(unit, function.origin(), args));
            }
        }

        boolean handled = false;
        List<MethodKey> targets = isJava(owner) ? List.of()
                : targetsOf(owner, name, descriptor, isStatic);
        for (MethodKey target : targets) {
            Unit callee = new Unit(target, context);
            int offset = 0;
            if (!isStatic) {
                joinFact("P:" + callee + "#0", withoutElements(receiver.tags()));
                offset = 1;
            }
            for (int each = 0; each < args.size(); each++) {
                joinFact("P:" + callee + "#" + (each + offset),
                        withoutElements(args.get(each).tags()));
            }
            enqueueOnce(callee);
            if (returnsAValue) {
                result.addAll(readFact("R:" + callee, unit));
                if (returnsAReference) {
                    result.addAll(elementsIn(receiver, args));
                }
            }
            if (!isStatic) {
                place(state, receiver, readFact("O:" + callee + "#0", unit));
            }
            for (int each = 0; each < args.size(); each++) {
                place(state, args.get(each), readFact("O:" + callee + "#" + (each + offset), unit));
            }
            handled = true;
        }
        if ((isJava(owner) || !handled) && !runsAFunction) {
            Call jdk = new Call(owner, name, descriptor, receiver, args, isStatic, returnsAValue,
                    returnsAReference, asksForExactlyOne.contains(key));
            String here = where + ":" + index + " " + owner.replace('/', '.') + "." + name;
            Outcome outcome = effectsOf(state, jdk, where, here);
            result.addAll(madeAt(outcome.result().tags(), here));
            made = outcome.result();
            for (Feed feed : outcome.feeds()) {
                for (Tag function : feed.functions()) {
                    Set<Tag> back = function.origin().startsWith("ref|")
                            ? runLibraryRef(state, function.origin(), feed.elements(), where, here)
                            : feedFunction(unit, function.origin(), feed.elements());
                    if (feed.returns()) {
                        result.addAll(back);
                    }
                    if (feed.keptBy() != null) {
                        place(state, feed.keptBy(), madeAt(SaltedOrderVocabulary.survivors(back,
                                false), here));
                    }
                    handBackWhatItFilled(unit, state, function.origin());
                }
            }
        }
        if (returnsAValue) {
            Set<Tag> kept = returnsAReference || keepsPositionInAnInt(name) ? result : Set.of();
            if (!SaltedOrderVocabulary.keepsTheElement(name)) {
                kept = Val.of(kept).madeOfTheElement().tags();
            }
            boolean heldInAMap = made != null && made.isHeldInAMap();
            int object = heldInAMap ? made.alloc()
                    : SaltedOrderVocabulary.makesAFreshNode(owner, name) ? index + 1 : -1;
            state.push(new Val(narrowed(kept, returns), isWide(type.returnType()), object,
                    made == null ? null : made.made(), heldInAMap ? made.home() : null));
        }
    }

    /**
     * What a call of the library does with what it is handed: the findings it makes, where it ends an
     * order, and what it puts in the objects it was given. The same whether the call is written as a
     * call or is run by a function that is a reference to it.
     */
    private Outcome effectsOf(State state, Call call, String where, String here) {
        Outcome outcome = SaltedOrderVocabulary.of(call);
        String owner = call.owner();
        String name = call.name();
        Set<String> origins = originsOf(call.tainted());
        if (SaltedOrderVocabulary.writesOut(owner, name)) {
            // A write is a sink whatever else is known of the call: what is written is written
            // in the order it has, and only the one there is has none.
            Set<Tag> written = new LinkedHashSet<>();
            for (Tag each : call.tainted()) {
                if (!each.isTheOnly()) {
                    written.add(each);
                }
            }
            if (!written.isEmpty()) {
                Set<String> sites = sitesOf(Val.of(written));
                note(where, "writes what came out of a copy to " + owner.replace('/', '.')
                        + "." + name + ", where it is written in the order the run gave"
                        + (sites.isEmpty() ? "" : "; an order made at " + sites),
                        originsOf(written));
            }
        } else if (outcome.unmodeled()) {
            Set<String> sites = sitesOf(Val.of(call.tainted()));
            note(where, (isJava(owner) ? "calls " : "hands what came out of a copy to ")
                    + owner.replace('/', '.') + "." + name
                    + (isJava(owner) ? " on what came out of a copy, and nothing says what that"
                            + " does with its order" : ", which is not read here")
                    + (sites.isEmpty() ? "" : "; an order made at " + sites), origins);
        }
        for (String by : outcome.crossedBy()) {
            reach(origins, "put in an order by " + by);
        }
        if (!outcome.endsAs().isEmpty()) {
            reach(origins, "read as " + outcome.endsAs());
        }
        // What is cleared is what the object held before the call, so what the call then puts in
        // is put in after it.
        for (Val each : outcome.clears()) {
            clear(state, each);
        }
        for (Push each : outcome.pushes()) {
            place(state, each.into(), madeAt(each.tags(), here));
        }
        return outcome;
    }

    /** What is a reference to a method of the library, and the values it was made over. */
    private record LibraryRef(Signature method, boolean isStatic, boolean isConstructor,
                              List<Val> captured) {}

    private final Map<String, LibraryRef> libraryRefs = new HashMap<>();

    /**
     * What a reference to a method of the library does when a walk runs it over elements: the call
     * it stands for, made with those. {@code out::add} run over the elements of a copy is the
     * adds of them in the order the walk met them, and is read as that.
     */
    private Set<Tag> runLibraryRef(State state, String function, List<Set<Tag>> elements,
                                   String where, String here) {
        LibraryRef ref = libraryRefs.get(function);
        if (ref == null) {
            return Set.of();
        }
        List<Val> given = new ArrayList<>();
        for (Set<Tag> each : elements) {
            given.add(Val.of(each));
        }
        if (ref.isConstructor()) {
            // What a constructor reference hands back is the object it made, holding what the
            // constructor put in it of what it was given.
            Val made = Val.CLEAN.withMade(ref.method().owner());
            Call built = new Call(ref.method().owner(), "<init>", ref.method().descriptor(), made,
                    given, false, false, false, false);
            Outcome outcome = effectsOf(state, built, where, here);
            Set<Tag> holding = new LinkedHashSet<>(outcome.result().tags());
            for (Push each : outcome.pushes()) {
                if (each.into() == made) {
                    holding.addAll(each.tags());
                }
            }
            return holding;
        }
        Val receiver;
        List<Val> args;
        if (ref.isStatic()) {
            receiver = Val.CLEAN;
            args = given;
        } else if (!ref.captured().isEmpty()) {
            receiver = ref.captured().get(0);
            args = given;
        } else if (!given.isEmpty()) {
            receiver = given.get(0);
            args = given.subList(1, given.size());
        } else {
            return Set.of();
        }
        MethodTypeDesc described = MethodTypeDesc.ofDescriptor(ref.method().descriptor());
        String returns = described.returnType().descriptorString();
        Call call = new Call(ref.method().owner(), ref.method().name(), ref.method().descriptor(),
                receiver, args, ref.isStatic(), !returns.equals("V"),
                returns.startsWith("L") || returns.startsWith("["), false);
        return effectsOf(state, call, where, here).result().tags();
    }

    private static boolean keepsPositionInAnInt(String name) {
        return name.equals("indexOf") || name.equals("lastIndexOf");
    }

    private static boolean isDerivingFunction(String name) {
        return switch (name) {
            case "andThen", "compose", "negate", "and", "or", "reversed", "thenComparing",
                 "thenComparingInt", "thenComparingLong", "thenComparingDouble", "equals",
                 "hashCode", "toString" -> true;
            default -> false;
        };
    }

    private static boolean isACopy(String owner, String name, int count) {
        boolean immutable = owner.equals("java/util/Set") || owner.equals("java/util/Map");
        if (!immutable) {
            return false;
        }
        return switch (name) {
            case "copyOf", "ofEntries" -> true;
            case "of" -> count >= (owner.equals("java/util/Set") ? 2 : 4);
            default -> false;
        };
    }

    /** What a function returns when its body is handed these, after what it captured. */
    private Set<Tag> callFunction(Unit caller, String function, List<Val> args) {
        Unit body = bodyOf(function);
        if (body == null) {
            return Set.of();
        }
        int offset = captured.getOrDefault(function, 0);
        for (int each = 0; each < args.size(); each++) {
            joinFact("P:" + body + "#" + (each + offset), args.get(each).tags());
        }
        enqueueOnce(body);
        return returnsOf(caller, body);
    }

    private Set<Tag> feedFunction(Unit caller, String function, List<Set<Tag>> elements) {
        Unit body = bodyOf(function);
        if (body == null) {
            return Set.of();
        }
        int offset = captured.getOrDefault(function, 0);
        for (int each = 0; each < elements.size(); each++) {
            joinFact("P:" + body + "#" + (each + offset), elements.get(each));
        }
        enqueueOnce(body);
        return returnsOf(caller, body);
    }

    /** What a function was made over, and the method that made it, which is where those are held. */
    private record Captured(Unit in, List<Val> values) {}

    private final Map<String, Captured> capturedAt = new HashMap<>();

    /**
     * What a function's body put into what it captured, as the method that made it sees it.
     *
     * <p>A function that fills a list it was given is the way a walk is written as {@code forEach},
     * so what it filled is what the list holds once the walk is over. Only where the function is
     * called from the method that made it: those are the places its captured values are still held.
     */
    private void handBackWhatItFilled(Unit here, State state, String function) {
        Captured made = capturedAt.get(function);
        Unit body = bodyOf(function);
        if (made == null || body == null || !made.in().equals(here)) {
            return;
        }
        for (int at = 0; at < made.values().size(); at++) {
            place(state, made.values().get(at), readFact("O:" + body + "#" + at, here));
        }
    }

    private Set<Tag> returnsOf(Unit caller, Unit body) {
        Set<Tag> out = new LinkedHashSet<>(readFact("R:" + body, caller));
        if (!body.context().isEmpty()) {
            out.addAll(readFact("R:" + new Unit(body.method(), ""), caller));
        }
        return out;
    }

    /** A function tag names its body and the place it was made, which is where it is read. */
    private Unit bodyOf(String function) {
        int bar = function.indexOf('|');
        String bodyKey = bar < 0 ? function : function.substring(0, bar);
        String context = bar < 0 ? "" : function.substring(bar + 1);
        int hash = bodyKey.indexOf('#');
        int paren = bodyKey.indexOf('(');
        if (hash < 0 || paren < 0) {
            return null;
        }
        MethodKey out = new MethodKey(bodyKey.substring(0, hash).replace('.', '/'),
                bodyKey.substring(hash + 1, paren), bodyKey.substring(paren));
        return methods.containsKey(out) ? new Unit(out, context) : null;
    }

    /** The methods a call may run: the one named, and what overrides it below. */
    private List<MethodKey> targetsOf(String owner, String name, String descriptor,
                                      boolean isStatic) {
        return runs.computeIfAbsent(new MethodKey(owner, name, descriptor + isStatic),
                k -> resolved(owner, name, descriptor, isStatic));
    }

    private List<MethodKey> resolved(String owner, String name, String descriptor,
                                     boolean isStatic) {
        List<MethodKey> out = new ArrayList<>();
        Set<String> seen = new LinkedHashSet<>();
        Deque<String> below = new ArrayDeque<>();
        below.add(owner);
        while (!below.isEmpty()) {
            String next = below.poll();
            if (!seen.add(next)) {
                continue;
            }
            MethodKey candidate = new MethodKey(next, name, descriptor);
            if (methods.containsKey(candidate)) {
                out.add(candidate);
            }
            if (!isStatic) {
                below.addAll(subs.getOrDefault(next, Set.of()));
            }
        }
        if (out.isEmpty()) {
            Deque<String> above = new ArrayDeque<>();
            above.add(owner);
            Set<String> visited = new LinkedHashSet<>();
            while (!above.isEmpty() && out.isEmpty()) {
                String next = above.poll();
                if (!visited.add(next)) {
                    continue;
                }
                MethodKey candidate = new MethodKey(next, name, descriptor);
                if (methods.containsKey(candidate)) {
                    out.add(candidate);
                }
                above.addAll(supers.getOrDefault(next, Set.of()));
            }
        }
        return out;
    }

    // ---- invokedynamic

    private void dynamic(Unit unit, InvokeDynamicInstruction dynamic, int index, State state) {
        MethodTypeDesc type = dynamic.typeSymbol();
        int count = type.parameterCount();
        List<Val> args = new ArrayList<>();
        for (int each = 0; each < count; each++) {
            args.add(0, state.pop());
        }
        DirectMethodHandleDesc bootstrap = dynamic.bootstrapMethod();
        String owner = bootstrap.owner().displayName();
        String returns = type.returnType().descriptorString();
        boolean wide = isWide(type.returnType());
        Set<Tag> result = new LinkedHashSet<>();
        if (owner.equals("LambdaMetafactory")) {
            DirectMethodHandleDesc body = null;
            for (var argument : dynamic.bootstrapArgs()) {
                if (argument instanceof DirectMethodHandleDesc handle) {
                    body = handle;
                }
            }
            if (body != null) {
                String bodyOwner = body.owner().descriptorString();
                bodyOwner = bodyOwner.substring(1, bodyOwner.length() - 1);
                MethodKey target = new MethodKey(bodyOwner, body.methodName(),
                        body.lookupDescriptor());
                String bodyKey = target.toString();
                if (methods.containsKey(target)) {
                    String context = unit.method() + ":" + index;
                    captured.merge(bodyKey + "|" + context, count, Math::max);
                    capturedAt.put(bodyKey + "|" + context, new Captured(unit, args));
                    Unit made = new Unit(target, context);
                    for (int each = 0; each < args.size(); each++) {
                        joinFact("P:" + made + "#" + each, args.get(each).tags());
                    }
                    // A function over a copy is read even where nothing in the program is seen to
                    // call it: it may be handed on as a value and called wherever that ends up.
                    if (carriesACopy(Val.CLEAN, args)) {
                        enqueueOnce(made);
                    }
                    result.add(new Tag(Kind.FUNCTION, bodyKey + "|" + context));
                } else {
                    for (Val each : args) {
                        result.addAll(each.tags());
                    }
                    Signature handle = new Signature(bodyOwner, body.methodName(),
                            body.lookupDescriptor());
                    if (SaltedOrderVocabulary.foldsInAnyOrder(handle)) {
                        result.add(SaltedOrderVocabulary.commutativeFunction(handle));
                    }
                    // A reference to a method nothing here reads is the call it stands for, run
                    // over whatever it is handed.
                    DirectMethodHandleDesc.Kind kind = body.kind();
                    String refKey = "ref|" + bodyOwner + "#" + body.methodName()
                            + body.lookupDescriptor() + "|" + unit.method() + ":" + index;
                    libraryRefs.put(refKey, new LibraryRef(handle,
                            kind == DirectMethodHandleDesc.Kind.STATIC
                                    || kind == DirectMethodHandleDesc.Kind.INTERFACE_STATIC,
                            kind == DirectMethodHandleDesc.Kind.CONSTRUCTOR, args));
                    result.add(new Tag(Kind.FUNCTION, refKey));
                }
            }
        } else if (owner.equals("StringConcatFactory")) {
            String here = unit + ":" + index + " joins into a text";
            for (int each = 0; each < args.size(); each++) {
                for (Tag tag : args.get(each).tags()) {
                    if (tag.cameOutOfACopy()) {
                        result.add(tag.kind() == Kind.PICKED || tag.kind() == Kind.CHOSEN ? tag
                                : new Tag(Kind.SEQUENCE, tag.origin()).madeAt(here));
                    }
                }
                // A text of an object says what its class's toString says, which for a record is
                // every field it holds, and one of them may be what a copy made.
                String held = type.parameterType(each).descriptorString();
                if (held.startsWith("L") && !isJava(held.substring(1))) {
                    result.addAll(madeAt(textOfTheFieldsOf(unit,
                            held.substring(1, held.length() - 1)), here));
                }
            }
        } else if (owner.equals("ObjectMethods")) {
            String what = dynamic.name().stringValue();
            if (what.equals("toString") && !args.isEmpty()) {
                result.addAll(madeAt(textOfARecord(unit, dynamic),
                        unit + ":" + index + " a record's own toString"));
            }
        }
        if (!returns.equals("V")) {
            boolean reference = returns.startsWith("L") || returns.startsWith("[");
            state.push(new Val(reference ? narrowed(result, returns) : Set.of(), wide, -1, null,
                    null));
        }
    }

    /** What a record's own {@code toString} says of the fields that hold what a copy made. */
    private Set<Tag> textOfARecord(Unit reader, InvokeDynamicInstruction dynamic) {
        String record = dynamic.typeSymbol().parameterList().get(0).descriptorString();
        return textOfTheFieldsOf(reader, record.substring(1, record.length() - 1));
    }

    private Set<Tag> textOfTheFieldsOf(Unit reader, String owner) {
        Set<Tag> out = new LinkedHashSet<>();
        readers.computeIfAbsent("C:" + owner, k -> new HashSet<>()).add(reader);
        for (String field : fieldsOf.getOrDefault(owner, Set.of())) {
            for (Tag tag : facts.getOrDefault(field, Set.of())) {
                if (tag.cameOutOfACopy()) {
                    out.add(new Tag(Kind.SEQUENCE, tag.origin()));
                }
            }
        }
        return out;
    }
}
