package souther.architecture;

import java.lang.classfile.Attributes;
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
import java.lang.classfile.instruction.ThrowInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.constant.MethodTypeDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

/**
 * One method, read as the ways control can go through it, for what it does with the models it
 * meets.
 *
 * <p>A model is a value held in a local variable, a field, or the answer of a call, and what the
 * test is held to is that it cannot pass without that model having been handed to the helper. So
 * the walk follows the standing of each local variable down every way through the method and joins
 * the standings where ways meet, and a read counts only where the model stands as asked about on
 * every way to it, or is asked about on every way out of the method after it. A way that leaves a
 * {@code try} for its handler is a way, taken from before the call that may have thrown.
 *
 * <p>What a call does with a model it is handed, and what a method answers or keeps in a field, is
 * a fact about another method, and is read from {@link Facts}, which the caller goes round until it
 * stops changing.
 */
final class ModelWalk {

    static final String COMPILATION = ModelVocabulary.COMPILATION;

    static final String COMPILATION_TYPE = ModelVocabulary.COMPILATION_TYPE;

    static final String REPORT = ModelVocabulary.REPORT;

    private static final String DB = ModelVocabulary.DB;

    private static final String DB_TYPE = ModelVocabulary.DB_TYPE;

    private static final String NOT_COMPILED = ModelVocabulary.NOT_COMPILED;

    private static final String ANSWER = "souther/compiler/query/Answer";

    /** What marks a method the test engine runs, handing it what its parameters ask for. */
    private static final Set<String> RUN_BY_THE_ENGINE = Set.of(
            "Lorg/junit/jupiter/api/Test;", "Lorg/junit/jupiter/api/RepeatedTest;",
            "Lorg/junit/jupiter/api/TestFactory;", "Lorg/junit/jupiter/api/TestTemplate;",
            "Lorg/junit/jupiter/params/ParameterizedTest;", "Lorg/junit/jupiter/api/BeforeEach;",
            "Lorg/junit/jupiter/api/BeforeAll;", "Lorg/junit/jupiter/api/AfterEach;",
            "Lorg/junit/jupiter/api/AfterAll;");


    /**
     * What the walks of every method have found about the others so far.
     *
     * @param returns            what a method answers that was not one of its arguments
     * @param returnsParameter   the arguments a method answers, as {@code method#index}
     * @param readsParameter     the arguments a method reads what is said of before it asks about
     *                           them
     * @param readsReportParameter the arguments a method reads a report of, and not only what the
     *                           declarations say
     * @param readsStrictParameter the arguments a method reads what is said of, and not only the
     *                           errors, which a model that was answered shows
     * @param asksParameter      the arguments a method asks about on every way through it
     * @param mutatesParameter   the arguments a method changes, or hands to what does
     * @param leavesAsked        the arguments a method leaves asked about on every way out, whatever
     *                           it did to them on the way
     * @param fields             what is written into each field of a model
     * @param fieldFlows         the fields an argument of a method is written into
     * @param changingMethods    the methods that change some argument they are handed
     * @param storeReturns       what the model each method that answers a store hands back the
     *                           store of stands as
     * @param storesMadeAlone    the methods that answer a store, and answer on every way out one
     *                           that they made with {@code new} and nothing else, which no model
     *                           owns
     */
    record Facts(Map<String, ModelStanding> returns, Set<String> returnsParameter,
                 Set<String> readsParameter, Set<String> readsReportParameter,
                 Set<String> readsStrictParameter, Set<String> asksParameter, Set<String> mutatesParameter,
                 Set<String> leavesAsked, Map<String, ModelStanding> fields,
                 Map<String, Set<String>> fieldFlows, Set<String> changingMethods,
                 Map<String, ModelStanding> storeReturns, Set<String> storesMadeAlone) {

        static final Facts NONE = new Facts(Map.of(), Set.of(), Set.of(), Set.of(), Set.of(),
                Set.of(), Set.of(), Set.of(), Map.of(), Map.of(), Set.of(), Map.of(), Set.of());
    }

    /**
     * What does not change while the facts are found.
     *
     * @param helper    the class a test goes through to ask that a model compiles
     * @param analysed  the methods that are walked
     * @param written   the fields a model is written into somewhere that is walked
     * @param captured  how many arguments each method that stands for a lambda is handed by the
     *                  one that made it
     * @param exempt    the methods that may read a model they did not compile, and say so
     * @param effects   what the methods of every class do to a model, worked out from the classes,
     *                  and which methods a call may run
     */
    record World(String helper, Set<String> analysed, Set<String> written,
                 Map<String, Integer> captured, Set<String> exempt, ModelEffects effects) { }

    /** What holds a model where it is used. */
    sealed interface Operand {

        /** A local variable. */
        record Local(int slot) implements Operand { }

        /** The answer of the call at {@code at}. */
        record Answer(InvokeInstruction call, int at) implements Operand { }

        /**
         * A field.
         *
         * @param sole it is the one a static field is, or the field of the object this method is
         *             run on, so that what is written to it is written to the only one there is;
         *             a field of another object is one of as many as there are objects
         */
        record Field(String key, boolean sole) implements Operand { }

        /** A store made here with {@code new}, which belongs to no model. */
        record FreshStore() implements Operand { }

        /** No model at all, which a read stops on. */
        record Nothing() implements Operand { }

        /** Something the walk cannot place. */
        record Lost() implements Operand { }
    }

    /**
     * A call at {@code at} that is given a model as one of its arguments.
     *
     * @param report    what the call reads is a report, which is empty for a model nothing was
     *                  asked of, and not only what the declarations say
     * @param exempts   the call says the model is read without being compiled, where that is
     *                  allowed
     * @param creation  the call makes a lambda that is handed the model, which does nothing with
     *                  it until the lambda is run, so what the lambda asks has not been asked
     * @param mutates   the call changes what the model is compiled from or how, so that what was
     *                  asked of it before is no longer what it is
     * @param store     what holds the store the call is given or is made on, where it is one, and
     *                  {@link Operand.Nothing} where it is not; the model is the one the store was
     *                  got from, where that can be told
     */
    record Site(int at, String callee, int parameter, boolean readsDirectly, boolean report,
                boolean asksDirectly, boolean exempts, boolean creation, boolean mutates,
                Operand operand, Operand store, boolean answers, boolean strict) { }

    /** What one walk found. */
    static final class Result {
        /** Which reads were refused, for the one who has to read why. */
        final List<String> notes = new ArrayList<>();
        /** Reads of a model that was never asked about. */
        int unasked;
        /** Reads of a model whose origin could not be placed. */
        int lost;
        /** Reads of a model that was asked about, by this method. */
        int asked;
        ModelStanding returns = ModelStanding.ASKED;
        /** What the model a store that is answered belongs to stands as, joined over the answers. */
        ModelStanding returnsStore = ModelStanding.ASKED;
        /** Whether every store it answers is one it made, so that it is of no model. */
        boolean returnsOnlyStoresItMade = true;
        final Set<Integer> returnsParameter = new HashSet<>();
        final Set<Integer> readsParameter = new HashSet<>();
        final Set<Integer> readsReportParameter = new HashSet<>();
        final Set<Integer> readsStrictParameter = new HashSet<>();
        final Set<Integer> asksParameter = new HashSet<>();
        final Set<Integer> mutatesParameter = new HashSet<>();
        /** How each argument stands, joined over the ways out of the method. */
        final Map<Integer, ModelStanding> exits = new HashMap<>();
        final Map<String, ModelStanding> fieldWrites = new HashMap<>();
        final Map<String, Set<String>> fieldFlows = new HashMap<>();
    }

    private final ClassModel owner;
    private final MethodModel method;
    private final String key;
    private final List<CodeElement> flow = new ArrayList<>();
    private final int[][] next;
    private final int[][] handlers;
    private final Map<Integer, Integer> parameterAt = new HashMap<>();
    private final Set<Integer> modelParameters = new HashSet<>();
    private final Set<Integer> storeParameters = new HashSet<>();
    private final Set<Integer> stored = new HashSet<>();
    private final Map<Integer, Integer> storeCounts = new HashMap<>();
    private Map<Integer, Set<Integer>> groups;
    private final Set<String> fieldsWritten = new HashSet<>();
    private final Map<String, Integer> capturedByLambdas = new HashMap<>();
    private final Map<Long, Operand> producers = new HashMap<>();
    private final Set<String> modelFields = new TreeSet<>();
    private final List<String> modelFieldOrder;
    private final List<Escape> escapes = new ArrayList<>();
    private final List<String> creations = new ArrayList<>();
    private final boolean relevant;
    private final boolean engineRuns;
    private Map<Integer, List<Site>> sites;

    private Facts facts;
    private World world;
    private Map<Integer, Set<Integer>> asks;
    private Map<Integer, Set<Integer>> mutations;
    private Set<Integer> mutatesAnyAt;
    private Map<Integer, Map<String, Set<Integer>>> tied;
    private final Map<Integer, boolean[]> reached = new HashMap<>();
    private List<List<Integer>> predecessors;
    private List<Map<Integer, ModelStanding>> in;
    private final Map<Integer, boolean[]> looked = new HashMap<>();

    ModelWalk(ClassModel owner, MethodModel method, String helper) {
        this.owner = owner;
        this.method = method;
        this.key = AMethod.of(owner, method);
        List<CodeElement> elements = method.code().orElseThrow().elementList();
        List<ExceptionCatch> catches = new ArrayList<>();
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
                case ExceptionCatch catching -> {
                    catches.add(catching);
                    landings.add(catching.handler());
                    landings.add(catching.tryStart());
                    landings.add(catching.tryEnd());
                }
                default -> { }
            }
        }
        Map<Label, Integer> landedAt = new HashMap<>();
        for (CodeElement element : elements) {
            if (element instanceof LabelTarget at && landings.contains(at.label())) {
                landedAt.put(at.label(), flow.size());
                flow.add(element);
            } else if (element instanceof Instruction) {
                flow.add(element);
            }
        }
        int size = flow.size();
        next = new int[size][];
        for (int i = 0; i < size; i++) {
            next[i] = successors(i, landedAt);
        }
        List<List<Integer>> handling = new ArrayList<>();
        for (int i = 0; i < size; i++) {
            handling.add(new ArrayList<>());
        }
        for (ExceptionCatch catching : catches) {
            int from = landedAt.get(catching.tryStart());
            int to = landedAt.get(catching.tryEnd());
            for (int at = from; at < to; at++) {
                if (flow.get(at) instanceof Instruction) {
                    handling.get(at).add(landedAt.get(catching.handler()));
                }
            }
        }
        handlers = new int[size][];
        for (int i = 0; i < size; i++) {
            handlers[i] = handling.get(i).stream().mapToInt(Integer::intValue).toArray();
        }
        int slot = method.flags().has(AccessFlag.STATIC) ? 0 : 1;
        int index = 0;
        for (ClassDesc parameter : method.methodTypeSymbol().parameterList()) {
            parameterAt.put(slot, index);
            if (parameter.descriptorString().equals(COMPILATION_TYPE)) {
                modelParameters.add(slot);
            }
            if (parameter.descriptorString().equals(DB_TYPE)) {
                storeParameters.add(slot);
            }
            index++;
            slot += sizeOf(parameter);
        }
        boolean mentions = method.methodTypeSymbol().descriptorString().contains(COMPILATION_TYPE)
                || method.methodTypeSymbol().descriptorString().contains(DB_TYPE);
        for (CodeElement element : flow) {
            switch (element) {
                case StoreInstruction store when store.typeKind() == TypeKind.REFERENCE -> {
                    stored.add(store.slot());
                    storeCounts.merge(store.slot(), 1, Integer::sum);
                }
                case FieldInstruction field -> {
                    if (field.typeSymbol().descriptorString().equals(COMPILATION_TYPE)) {
                        mentions = true;
                        modelFields.add(fieldKey(field));
                        if (field.opcode() == Opcode.PUTFIELD || field.opcode() == Opcode.PUTSTATIC) {
                            fieldsWritten.add(fieldKey(field));
                        }
                    }
                }
                case InvokeInstruction call -> {
                    String name = call.owner().asInternalName();
                    mentions |= name.equals(COMPILATION) || name.equals(REPORT)
                            || name.equals(DB) || isHelper(name, helper)
                            || call.type().stringValue().contains(COMPILATION_TYPE)
                            || call.type().stringValue().contains(DB_TYPE);
                }
                case InvokeDynamicInstruction call -> {
                    mentions |= call.type().stringValue().contains(COMPILATION_TYPE)
                            || call.type().stringValue().contains(DB_TYPE);
                    String impl = lambdaImplementation(call);
                    if (impl != null) {
                        capturedByLambdas.merge(impl, capturedArguments(call), Math::max);
                    }
                }
                default -> { }
            }
        }
        this.modelFieldOrder = List.copyOf(modelFields);
        this.relevant = mentions;
        this.engineRuns = method.findAttribute(Attributes.runtimeVisibleAnnotations())
                .map(found -> found.annotations().stream().anyMatch(each ->
                        RUN_BY_THE_ENGINE.contains(each.classSymbol().descriptorString())))
                .orElse(false);
    }

    /** Whether the method answers a store. */
    boolean handsBackAStore() {
        return method.methodTypeSymbol().returnType().descriptorString().equals(DB_TYPE);
    }

    /** Whether the test engine runs the method, handing it what its parameters ask for. */
    boolean engineRuns() {
        return engineRuns;
    }

    String key() {
        return key;
    }

    ClassModel owner() {
        return owner;
    }

    MethodModel method() {
        return method;
    }

    /** Whether the method has anything to do with a model. */
    boolean relevant() {
        return relevant;
    }

    Set<String> fieldsWritten() {
        return fieldsWritten;
    }

    /** The parameters of other methods that the calls of this one hand a model to. */
    Set<String> handedOn() {
        Set<String> handed = new HashSet<>();
        for (List<Site> here : sites(world.helper()).values()) {
            for (Site site : here) {
                for (String target : world.effects().targets(site.callee())) {
                    handed.add(target + "#" + site.parameter());
                }
            }
        }
        return handed;
    }

    Map<String, Integer> capturedByLambdas() {
        return capturedByLambdas;
    }

    private int[] successors(int at, Map<Label, Integer> landedAt) {
        CodeElement element = flow.get(at);
        boolean last = at + 1 >= flow.size();
        return switch (element) {
            case BranchInstruction branch -> {
                int target = landedAt.get(branch.target());
                boolean always = branch.opcode() == Opcode.GOTO
                        || branch.opcode() == Opcode.GOTO_W;
                yield always || last ? new int[] {target} : new int[] {target, at + 1};
            }
            case LookupSwitchInstruction table -> {
                List<Integer> out = new ArrayList<>();
                out.add(landedAt.get(table.defaultTarget()));
                table.cases().stream().map(SwitchCase::target).map(landedAt::get)
                        .forEach(out::add);
                yield out.stream().mapToInt(Integer::intValue).toArray();
            }
            case TableSwitchInstruction table -> {
                List<Integer> out = new ArrayList<>();
                out.add(landedAt.get(table.defaultTarget()));
                table.cases().stream().map(SwitchCase::target).map(landedAt::get)
                        .forEach(out::add);
                yield out.stream().mapToInt(Integer::intValue).toArray();
            }
            case ReturnInstruction _, ThrowInstruction _ -> new int[0];
            default -> last ? new int[0] : new int[] {at + 1};
        };
    }

    /** What the walk found, given what is known of the other methods. */
    Result run(Facts known, World knownWorld) {
        this.facts = known;
        this.world = knownWorld;
        looked.clear();
        tied = null;
        int size = flow.size();
        Map<Integer, List<Site>> all = withEscapes(sites(knownWorld.helper()));
        asks = new HashMap<>();
        mutations = new HashMap<>();
        mutatesAnyAt = new HashSet<>();
        for (List<Site> here : all.values()) {
            for (Site site : here) {
                if (asking(site) && site.operand() instanceof Operand.Local local) {
                    for (int member : membersOf(local.slot())) {
                        asks.computeIfAbsent(member, s -> new HashSet<>()).add(site.at());
                    }
                }
                if (mutating(site)) {
                    if (site.operand() instanceof Operand.Local local) {
                        for (int member : membersOf(local.slot())) {
                            mutations.computeIfAbsent(member, s -> new HashSet<>())
                                    .add(site.at());
                        }
                        if (givenOnSeveralWays(local.slot(), site.at())) {
                            mutatesAnyAt.add(site.at());
                        }
                    } else if (!noModel(site.operand())) {
                        mutatesAnyAt.add(site.at());
                    }
                }
            }
        }
        in = new ArrayList<>(Collections.nCopies(size, null));
        Result result = new Result();
        if (size == 0) {
            return result;
        }
        Map<Integer, ModelStanding> entry = new HashMap<>();
        for (int slot : modelParameters) {
            entry.put(slot, ModelStanding.HANDED_IN);
        }
        for (int slot : storeParameters) {
            entry.put(slot, ModelStanding.HANDED_IN);
        }
        for (String each : modelFieldOrder) {
            entry.put(fieldSlot(each), field(each));
        }
        in.set(0, entry);
        Deque<Integer> work = new ArrayDeque<>();
        work.add(0);
        while (!work.isEmpty()) {
            int at = work.poll();
            Map<Integer, ModelStanding> before = in.get(at);
            Map<Integer, ModelStanding> after = transfer(at, before, all);
            for (int to : next[at]) {
                merge(to, after, work);
            }
            for (int to : handlers[at]) {
                merge(to, before, work);
                merge(to, after, work);
                merge(to, abrupt(at, before, all), work);
            }
        }
        for (int at = 0; at < size; at++) {
            if (in.get(at) != null) {
                account(at, all, result);
            }
        }
        for (int slot : modelParameters) {
            if (!stored.contains(slot) && lookedAfter(slot)[0]) {
                result.asksParameter.add(parameterAt.get(slot));
            }
        }
        return result;
    }

    private void merge(int to, Map<Integer, ModelStanding> state, Deque<Integer> work) {
        Map<Integer, ModelStanding> held = in.get(to);
        if (held == null) {
            in.set(to, new HashMap<>(state));
            work.add(to);
            return;
        }
        Map<Integer, ModelStanding> joined = null;
        for (Map.Entry<Integer, ModelStanding> each : state.entrySet()) {
            ModelStanding was = held.get(each.getKey());
            ModelStanding now = was == null ? each.getValue() : was.join(each.getValue());
            if (now != was) {
                if (joined == null) {
                    joined = new HashMap<>(held);
                }
                joined.put(each.getKey(), now);
            }
        }
        if (joined != null) {
            in.set(to, joined);
            work.add(to);
        }
    }

    private Map<Integer, ModelStanding> transfer(int at, Map<Integer, ModelStanding> state,
                                                 Map<Integer, List<Site>> all) {
        CodeElement element = flow.get(at);
        if (element instanceof StoreInstruction store && store.typeKind() == TypeKind.REFERENCE) {
            Map<Integer, ModelStanding> out = new HashMap<>(state);
            out.put(store.slot(), standing(producer(at, 0), state));
            return out;
        }
        if (element instanceof FieldInstruction put
                && (put.opcode() == Opcode.PUTFIELD || put.opcode() == Opcode.PUTSTATIC)
                && modelFields.contains(fieldKey(put))) {
            Map<Integer, ModelStanding> out = new HashMap<>(state);
            ModelStanding written = standing(producer(at, 0), state);
            int place = fieldSlot(fieldKey(put));
            // A write to a field of another object may be to any of as many fields as there are
            // objects, so it does not say of the one read afterwards what it says of the one
            // written: the field stands as the worse of what it stood as and what is written.
            out.put(place, soleReceiver(put, at) ? written
                    : state.getOrDefault(place, field(fieldKey(put))).join(written));
            return out;
        }
        List<Site> here = all.get(at);
        if (here == null) {
            return state;
        }
        Map<Integer, ModelStanding> out = null;
        for (Site site : here) {
            if (site.operand() instanceof Operand.Local local) {
                ModelStanding becomes = mutating(site) ? ModelStanding.UNASKED
                        : asking(site) ? ModelStanding.ASKED
                        : site.exempts() ? ModelStanding.EXEMPT
                        : site.answers() && state.get(local.slot()) != ModelStanding.ASKED
                        ? ModelStanding.ANSWERED : null;
                if (becomes != null) {
                    if (out == null) {
                        out = new HashMap<>(state);
                    }
                    for (int member : membersOf(local.slot())) {
                        out.put(member, becomes);
                    }
                    if (becomes == ModelStanding.UNASKED
                            && givenOnSeveralWays(local.slot(), site.at())) {
                        out.replaceAll((slot, standing) -> ModelStanding.UNASKED);
                    }
                }
            } else if (site.operand() instanceof Operand.Field field
                    && modelFields.contains(field.key())) {
                ModelStanding becomes = mutating(site) ? ModelStanding.UNASKED
                        : field.sole() && asking(site) ? ModelStanding.ASKED
                        : field.sole() && site.answers() && state.get(fieldSlot(field.key()))
                                != ModelStanding.ASKED ? ModelStanding.ANSWERED : null;
                if (becomes != null) {
                    if (out == null) {
                        out = new HashMap<>(state);
                    }
                    out.put(fieldSlot(field.key()), becomes);
                }
            } else if (mutating(site) && !noModel(site.operand())) {
                if (out == null) {
                    out = new HashMap<>(state);
                }
                out.replaceAll((slot, standing) -> ModelStanding.UNASKED);
            }
        }
        return out == null ? state : out;
    }

    /** Whether the field the node at {@code at} writes is the only one: a static, or this one's. */
    private boolean soleReceiver(FieldInstruction put, int at) {
        return put.opcode() == Opcode.PUTSTATIC || (producer(at, 1) instanceof Operand.Local held
                && held.slot() == 0 && !method.flags().has(AccessFlag.STATIC));
    }

    /** Whether the object the field read at {@code at} is of is the one this method is run on. */
    private boolean onThis(int at) {
        return at > 0 && flow.get(at - 1) instanceof LoadInstruction held
                && held.typeKind() == TypeKind.REFERENCE && held.slot() == 0
                && !method.flags().has(AccessFlag.STATIC);
    }

    /**
     * Whether the variable is given a value in more than one place, so that the model it holds
     * where it is changed may be any that it is given and is not told by the variable alone.
     */
    private boolean givenOnSeveralWays(int slot, int at) {
        if (storeCounts.getOrDefault(slot, 0) < 2 && !modelParameters.contains(slot)) {
            return false;
        }
        boolean[] seen = new boolean[flow.size()];
        Deque<Integer> work = new ArrayDeque<>(predecessorsOf(at));
        int given = 0;
        boolean fromTheStart = at == 0;
        while (!work.isEmpty()) {
            int node = work.poll();
            if (seen[node]) {
                continue;
            }
            seen[node] = true;
            if (flow.get(node) instanceof StoreInstruction store
                    && store.typeKind() == TypeKind.REFERENCE && store.slot() == slot) {
                if (!(producer(node, 0) instanceof Operand.Nothing)) {
                    given++;
                }
                continue;
            }
            if (node == 0) {
                fromTheStart = true;
            }
            work.addAll(predecessorsOf(node));
        }
        return given + (fromTheStart && modelParameters.contains(slot) ? 1 : 0) > 1;
    }

    private List<Integer> predecessorsOf(int node) {
        if (predecessors == null) {
            predecessors = new ArrayList<>();
            for (int i = 0; i < flow.size(); i++) {
                predecessors.add(new ArrayList<>());
            }
            for (int from = 0; from < flow.size(); from++) {
                for (int to : next[from]) {
                    predecessors.get(to).add(from);
                }
                for (int to : handlers[from]) {
                    predecessors.get(to).add(from);
                }
            }
        }
        return predecessors.get(node);
    }

    /** The place a field that holds a model has among the variables the walk keeps standings of. */
    private int fieldSlot(String field) {
        return -1 - modelFieldOrder.indexOf(field);
    }

    /**
     * What the variables stand as when the node at {@code at} fails after changing what it was
     * given. A method that returns with a model asked about may have changed it before it failed,
     * so a handler that takes the failure does not get what the method says of the way it returns.
     */
    private Map<Integer, ModelStanding> abrupt(int at, Map<Integer, ModelStanding> before,
                                               Map<Integer, List<Site>> all) {
        Map<Integer, ModelStanding> out = null;
        for (Site site : all.getOrDefault(at, List.of())) {
            if (!changes(site)) {
                continue;
            }
            if (noModel(site.operand())) {
                continue;
            }
            if (out == null) {
                out = new HashMap<>(before);
            }
            if (site.operand() instanceof Operand.Local local) {
                for (int member : membersOf(local.slot())) {
                    out.put(member, ModelStanding.UNASKED);
                }
            } else {
                out.replaceAll((slot, standing) -> ModelStanding.UNASKED);
            }
        }
        return out == null ? before : out;
    }

    /**
     * Whether the call changes the model it is handed, or may: it is a change to what the model is
     * compiled from, or it is handed to a method that changes it, or to code of the compiler that
     * is not walked and so is not known not to.
     */
    private boolean mutating(Site site) {
        return changes(site) && !everyTargetFact(facts.leavesAsked(), site);
    }

    /**
     * Whether the call may change the model on some way it can go, which includes the way out
     * through a failure. A method that leaves a model asked about on every way it returns has
     * still changed it on the way that throws.
     */
    private boolean changes(Site site) {
        return site.mutates() || anyTargetFact(facts.mutatesParameter(), site)
                || handedToCodeThatChangesIt(site);
    }

    /**
     * Whether the call hands the model, or the store of one, to code that is not walked and can
     * reach a change to a model, which {@link ModelEffects} works out over what the call may run.
     */
    private boolean handedToCodeThatChangesIt(Site site) {
        if (site.creation()) {
            return false;
        }
        for (String target : world.effects().targets(site.callee())) {
            String owner = target.substring(0, target.indexOf('#'));
            if (owner.startsWith("souther/") && !owner.equals(COMPILATION)
                    && !owner.equals(REPORT) && !owner.equals(DB)
                    && !isHelper(owner, world.helper()) && !world.analysed().contains(target)
                    && world.effects().changes(target)) {
                return true;
            }
        }
        return false;
    }

    /** Whether the fact holds of the argument for some method the call may run. */
    private boolean anyTargetFact(Set<String> fact, Site site) {
        for (String target : world.effects().targets(site.callee())) {
            if (fact.contains(target + "#" + site.parameter())) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether the fact holds of the argument for every method the call may run that has a body,
     * and there is one. A method that is not walked has no facts, so it never holds.
     */
    private boolean everyTargetFact(Set<String> fact, Site site) {
        boolean any = false;
        for (String target : world.effects().targets(site.callee())) {
            if (world.effects().hasCode(target)) {
                any = true;
                if (!fact.contains(target + "#" + site.parameter())) {
                    return false;
                }
            }
        }
        return any;
    }

    /**
     * Whether the model in {@code slot} is asked about on every way from just after the node at
     * {@code at} out of the method. What the node itself does does not count, so that a call that
     * reads a model and asks about it afterwards is not excused of the read by the asking.
     */
    private boolean afterNode(int slot, int at) {
        boolean[] held = lookedAfter(slot);
        CodeElement element = flow.get(at);
        boolean value;
        if (element instanceof ReturnInstruction) {
            value = false;
        } else if (element instanceof ThrowInstruction) {
            value = engineRuns;
        } else if (next[at].length == 0) {
            value = false;
        } else {
            value = true;
            for (int to : next[at]) {
                value &= held[to];
            }
        }
        for (int to : handlers[at]) {
            value &= held[to];
        }
        return value;
    }

    /**
     * The variables that hold the model {@code slot} holds: those it was copied to, or copied
     * from, where each is given a model once and so holds the same one on every way through.
     */
    private Set<Integer> membersOf(int slot) {
        if (groups == null) {
            groups = new HashMap<>();
            for (int at = 0; at < flow.size(); at++) {
                if (flow.get(at) instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE
                        && producer(at, 0) instanceof Operand.Local from
                        && storeCounts.getOrDefault(from.slot(), 0) <= 1
                        && storeCounts.getOrDefault(store.slot(), 0) == 1) {
                    Set<Integer> joined = new HashSet<>(groups.getOrDefault(from.slot(),
                            Set.of(from.slot())));
                    joined.addAll(groups.getOrDefault(store.slot(), Set.of(store.slot())));
                    for (int member : joined) {
                        groups.put(member, joined);
                    }
                }
            }
        }
        return groups.getOrDefault(slot, Set.of(slot));
    }

    private boolean asking(Site site) {
        return !site.creation() && (site.asksDirectly()
                || everyTargetFact(facts.asksParameter(), site)
                || everyTargetFact(facts.leavesAsked(), site));
    }

    private boolean reading(Site site) {
        return site.readsDirectly() || anyTargetFact(facts.readsParameter(), site);
    }

    private Set<String> fieldsFlowingTo(Site site) {
        Set<String> found = new HashSet<>();
        for (String target : world.effects().targets(site.callee())) {
            found.addAll(facts.fieldFlows().getOrDefault(target + "#" + site.parameter(),
                    Set.of()));
        }
        return found;
    }

    /**
     * The fields the model a variable holds is also held by: those it was written into, those it
     * was read out of, and those a method it was handed to writes it into. Changing the model by
     * way of the variable is a change to what the field holds, which a field stands for on every
     * way and not at one place.
     */
    private Set<String> fieldsTiedTo(int slot, int changedAt) {
        if (tied == null) {
            tied = new HashMap<>();
            for (int at = 0; at < flow.size(); at++) {
                switch (flow.get(at)) {
                    case FieldInstruction field when (field.opcode() == Opcode.PUTFIELD
                            || field.opcode() == Opcode.PUTSTATIC)
                            && field.typeSymbol().descriptorString().equals(COMPILATION_TYPE) -> {
                        if (producer(at, 0) instanceof Operand.Local held) {
                            tie(held.slot(), fieldKey(field), at);
                        }
                    }
                    case StoreInstruction store when store.typeKind() == TypeKind.REFERENCE -> {
                        if (producer(at, 0) instanceof Operand.Field from) {
                            tie(store.slot(), from.key(), at);
                        }
                    }
                    default -> { }
                }
            }
            for (List<Site> here : sites(world.helper()).values()) {
                for (Site site : here) {
                    if (site.operand() instanceof Operand.Local held) {
                        for (String field : fieldsFlowingTo(site)) {
                            tie(held.slot(), field, site.at());
                        }
                    }
                }
            }
        }
        Set<String> found = new HashSet<>();
        for (Map.Entry<String, Set<Integer>> each : tied.getOrDefault(slot, Map.of())
                .entrySet()) {
            for (int from : each.getValue()) {
                if (reachableFrom(from)[changedAt]) {
                    found.add(each.getKey());
                    break;
                }
            }
        }
        return found;
    }

    private void tie(int slot, String field, int at) {
        tied.computeIfAbsent(slot, k -> new HashMap<>())
                .computeIfAbsent(field, k -> new HashSet<>()).add(at);
    }

    /** The nodes that can run after the node at {@code from}, by any way including a handler. */
    private boolean[] reachableFrom(int from) {
        return reached.computeIfAbsent(from, start -> {
            boolean[] seen = new boolean[flow.size()];
            Deque<Integer> work = new ArrayDeque<>();
            for (int to : next[start]) {
                work.add(to);
            }
            for (int to : handlers[start]) {
                work.add(to);
            }
            while (!work.isEmpty()) {
                int at = work.poll();
                if (!seen[at]) {
                    seen[at] = true;
                    for (int to : next[at]) {
                        work.add(to);
                    }
                    for (int to : handlers[at]) {
                        work.add(to);
                    }
                }
            }
            return seen;
        });
    }

    /** What the node at {@code at} does, now that the standing of everything before it is known. */
    private void account(int at, Map<Integer, List<Site>> all, Result result) {
        Map<Integer, ModelStanding> state = in.get(at);
        CodeElement element = flow.get(at);
        for (Site site : all.getOrDefault(at, List.of())) {
            for (String field : fieldsFlowingTo(site)) {
                result.fieldWrites.merge(field, standing(site.operand(), state),
                        ModelStanding::join);
            }
            if (reading(site) && !(site.callee().equals(ESCAPE)
                    && standing(site.operand(), state) == ModelStanding.LOST)) {
                int refusedBefore = result.unasked + result.lost;
                read(site.operand(), at, state, result,
                        site.report() || anyTargetFact(facts.readsReportParameter(), site),
                        site.strict() || anyTargetFact(facts.readsStrictParameter(), site));
                if (result.unasked + result.lost > refusedBefore) {
                    result.notes.add("read by " + site.callee() + " of " + site.operand()
                            + " standing " + standing(site.operand(), state));
                }
            }
            if (changes(site)) {
                if (site.operand() instanceof Operand.Local local) {
                    for (int member : membersOf(local.slot())) {
                        if (modelParameters.contains(member) && !stored.contains(member)) {
                            result.mutatesParameter.add(parameterAt.get(member));
                        }
                    }
                }
                if (site.store() instanceof Operand.Local held
                        && storeParameters.contains(held.slot()) && !stored.contains(held.slot())) {
                    result.mutatesParameter.add(parameterAt.get(held.slot()));
                }
            }
            if (mutating(site)) {
                if (site.operand() instanceof Operand.Local local) {
                    for (int member : membersOf(local.slot())) {
                        for (String field : fieldsTiedTo(member, at)) {
                            result.fieldWrites.merge(field, ModelStanding.UNASKED,
                                    ModelStanding::join);
                        }
                    }
                } else if (site.operand() instanceof Operand.Field field
                        && !site.callee().equals(ESCAPE)) {
                    result.fieldWrites.merge(field.key(), ModelStanding.UNASKED,
                            ModelStanding::join);
                }
            }
        }
        if (element instanceof ReturnInstruction) {
            for (int slot : modelParameters) {
                if (!stored.contains(slot)) {
                    result.exits.merge(parameterAt.get(slot),
                            state.getOrDefault(slot, ModelStanding.HANDED_IN),
                            ModelStanding::join);
                }
            }
        }
        boolean returnsModel = method.methodTypeSymbol().returnType().descriptorString()
                .equals(COMPILATION_TYPE);
        if (element instanceof ReturnInstruction handedBack
                && handedBack.typeKind() == TypeKind.REFERENCE
                && method.methodTypeSymbol().returnType().descriptorString().equals(DB_TYPE)) {
            // What a store stands as is what the model it belongs to stands as, and a store a
            // method made is of no model.
            Operand of = modelOfTheDb(producer(at, 0));
            ModelStanding standing = noModel(of) ? ModelStanding.ASKED
                    : unhanded(standing(of, state));
            result.returnsStore = result.returnsStore.join(standing);
            result.returnsOnlyStoresItMade &= noModel(of);
        }
        if (element instanceof ReturnInstruction back && back.typeKind() == TypeKind.REFERENCE
                && returnsModel) {
            Operand operand = producer(at, 0);
            Integer parameter = pristineParameter(operand);
            ModelStanding standing = standing(operand, state);
            if (parameter != null && standing == ModelStanding.HANDED_IN) {
                result.returnsParameter.add(parameter);
            } else {
                result.returns = result.returns.join(unhanded(standing));
            }
        } else if (element instanceof FieldInstruction field
                && (field.opcode() == Opcode.PUTFIELD || field.opcode() == Opcode.PUTSTATIC)
                && field.typeSymbol().descriptorString().equals(COMPILATION_TYPE)) {
            Operand operand = producer(at, 0);
            Integer parameter = pristineParameter(operand);
            ModelStanding standing = standing(operand, state);
            if (parameter != null && standing == ModelStanding.HANDED_IN) {
                result.fieldFlows.computeIfAbsent(key + "#" + parameter, k -> new HashSet<>())
                        .add(fieldKey(field));
            } else {
                result.fieldWrites.merge(fieldKey(field), unhanded(standing),
                        ModelStanding::join);
            }
        }
    }

    /** A model that came in as an argument and was then moved about is one nobody can follow. */
    private static ModelStanding unhanded(ModelStanding standing) {
        return standing == ModelStanding.HANDED_IN ? ModelStanding.LOST : standing;
    }

    private Integer pristineParameter(Operand operand) {
        if (operand instanceof Operand.Local local
                && (modelParameters.contains(local.slot())
                || storeParameters.contains(local.slot()))
                && !stored.contains(local.slot())) {
            return parameterAt.get(local.slot());
        }
        return null;
    }

    private void read(Operand operand, int at, Map<Integer, ModelStanding> state, Result result,
                      boolean report, boolean strict) {
        ModelStanding standing = standing(operand, state);
        if (standing == ModelStanding.EXEMPT) {
            if (report) {
                result.unasked++;
            }
            return;
        }
        if (standing == ModelStanding.ANSWERED) {
            if (strict) {
                result.unasked++;
            } else {
                result.asked++;
            }
            return;
        }
        if (operand instanceof Operand.Local local) {
            boolean after = afterNode(local.slot(), at);
            if (standing == ModelStanding.ASKED) {
                if (asks.containsKey(local.slot())) {
                    result.asked++;
                }
                return;
            }
            if (after) {
                result.asked++;
                return;
            }
            Integer parameter = pristineParameter(operand);
            if (standing == ModelStanding.HANDED_IN && parameter != null) {
                result.readsParameter.add(parameter);
                if (report) {
                    result.readsReportParameter.add(parameter);
                }
                if (strict) {
                    result.readsStrictParameter.add(parameter);
                }
                if (method.methodName().stringValue().startsWith("lambda$")
                        && parameter >= world.captured().getOrDefault(key, 0)) {
                    result.lost++;
                }
                return;
            }
            if (standing == ModelStanding.UNASKED) {
                result.unasked++;
            } else {
                result.lost++;
            }
            return;
        }
        switch (standing) {
            case ASKED, EXEMPT, ANSWERED -> { }
            case UNASKED -> result.unasked++;
            case HANDED_IN, LOST -> result.lost++;
        }
    }

    /** How the model {@code operand} holds stands, given the standing of the variables. */
    private ModelStanding standing(Operand operand, Map<Integer, ModelStanding> state) {
        return switch (operand) {
            case Operand.Lost _ -> ModelStanding.LOST;
            case Operand.Nothing _, Operand.FreshStore _ -> ModelStanding.ASKED;
            case Operand.Field field -> modelFields.contains(field.key())
                    ? state.getOrDefault(fieldSlot(field.key()), field(field.key()))
                    : field(field.key());
            case Operand.Local local -> state.getOrDefault(local.slot(), ModelStanding.HANDED_IN);
            case Operand.Answer answer -> answered(answer, state);
        };
    }

    private ModelStanding field(String field) {
        if (!world.written().contains(field)) {
            return ModelStanding.LOST;
        }
        return facts.fields().getOrDefault(field, ModelStanding.ASKED);
    }

    /**
     * Whether the model {@code operand} stands for is none: it is a store made here, or the answer
     * of a call that answers only stores it made, on every way out of every method it may run.
     */
    private boolean noModel(Operand operand) {
        return operand instanceof Operand.Nothing
                || (operand instanceof Operand.Answer made && made.call().typeSymbol().returnType()
                .descriptorString().equals(DB_TYPE) && madeAloneEverywhere(made.call()));
    }

    private boolean madeAloneEverywhere(InvokeInstruction call) {
        boolean any = false;
        String callee = AMethod.of(call.owner().asInternalName(), call.name().stringValue(),
                call.type().stringValue());
        for (String target : world.effects().targets(callee)) {
            if (!world.effects().hasCode(target)) {
                continue;
            }
            if (!facts.storesMadeAlone().contains(target)) {
                return false;
            }
            any = true;
        }
        return any;
    }

    /**
     * What the model stands as that the store the call answers belongs to, from every method the
     * call may run, and not placed where one of them is not walked.
     */
    private ModelStanding standingOfTheStore(InvokeInstruction call) {
        ModelStanding standing = ModelStanding.ASKED;
        boolean any = false;
        String callee = AMethod.of(call.owner().asInternalName(), call.name().stringValue(),
                call.type().stringValue());
        for (String target : world.effects().targets(callee)) {
            if (!world.effects().hasCode(target)) {
                continue;
            }
            ModelStanding of = facts.storeReturns().get(target);
            if (of == null) {
                return ModelStanding.LOST;
            }
            any = true;
            standing = standing.join(of);
        }
        return any ? standing : ModelStanding.LOST;
    }

    private ModelStanding answered(Operand.Answer answer, Map<Integer, ModelStanding> state) {
        InvokeInstruction call = answer.call();
        if (call.typeSymbol().returnType().descriptorString().equals(DB_TYPE)) {
            return standingOfTheStore(call);
        }
        if (!call.typeSymbol().returnType().descriptorString().equals(COMPILATION_TYPE)) {
            return ModelStanding.LOST;
        }
        String callee = call.owner().asInternalName();
        String name = call.name().stringValue();
        if (callee.equals(COMPILATION)) {
            if (call.opcode() == Opcode.INVOKESTATIC) {
                return name.startsWith("of") ? ModelStanding.UNASKED : ModelStanding.LOST;
            }
            return ModelStanding.UNASKED;
        }
        if (isHelper(callee, world.helper())) {
            if (name.equals(NOT_COMPILED)) {
                return world.exempt().contains(key) ? ModelStanding.EXEMPT : ModelStanding.LOST;
            }
            return ModelStanding.ASKED;
        }
        String method = AMethod.of(callee, name, call.type().stringValue());
        ModelStanding standing = ModelStanding.ASKED;
        boolean any = false;
        for (String target : world.effects().targets(method)) {
            if (!world.effects().hasCode(target)) {
                continue;
            }
            if (!world.analysed().contains(target)) {
                return ModelStanding.LOST;
            }
            any = true;
            standing = standing.join(facts.returns().getOrDefault(target, ModelStanding.ASKED));
        }
        if (!any) {
            return ModelStanding.LOST;
        }
        Map<Integer, ModelStanding> then = in.get(answer.at());
        for (Site site : sites(world.helper()).getOrDefault(answer.at(), List.of())) {
            if (anyTargetFact(facts.returnsParameter(), site)) {
                standing = standing.join(standing(site.operand(), then == null ? state : then));
            }
        }
        return standing;
    }

    /**
     * Whether the model in {@code slot} is asked about on every way from the node at each index to
     * a way out of the method, before the variable is given another.
     *
     * <p>Worked out from the ways out backwards, taking the meet over the ways on, so that a way
     * that can leave without having asked, or can step past the call, makes it false. The ways to
     * a handler count at every node a {@code try} covers, so a call whose failure is caught and
     * dropped is not one that asked.
     */
    private boolean[] lookedAfter(int slot) {
        return looked.computeIfAbsent(slot, this::lookedAfterComputed);
    }

    private boolean[] lookedAfterComputed(int slot) {
        int size = flow.size();
        Set<Integer> looks = asks.getOrDefault(slot, Set.of());
        boolean[] held = new boolean[size];
        Arrays.fill(held, true);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int at = size - 1; at >= 0; at--) {
                CodeElement element = flow.get(at);
                boolean value;
                if (looks.contains(at)) {
                    value = true;
                } else if (element instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE && store.slot() == slot) {
                    value = false;
                } else if (mutations.getOrDefault(slot, Set.of()).contains(at)
                        || mutatesAnyAt.contains(at)) {
                    value = false;
                } else if (element instanceof ReturnInstruction) {
                    value = false;
                } else if (element instanceof ThrowInstruction) {
                    value = engineRuns;
                } else if (next[at].length == 0) {
                    value = false;
                } else {
                    value = true;
                    for (int to : next[at]) {
                        value &= held[to];
                    }
                }
                for (int to : handlers[at]) {
                    value &= held[to];
                }
                if (held[at] && !value) {
                    held[at] = false;
                    changed = true;
                }
            }
        }
        return held;
    }

    /** The calls that are given a model, and what each does with it. */
    private Map<Integer, List<Site>> sites(String helper) {
        if (sites != null) {
            return sites;
        }
        Map<Integer, List<Site>> found = new HashMap<>();
        Set<Integer> configuring = new HashSet<>();
        for (int at = 0; at < flow.size(); at++) {
            if (flow.get(at) instanceof InvokeInstruction call
                    && call.opcode() != Opcode.INVOKESTATIC
                    && call.owner().asInternalName().equals(DB)
                    && ModelVocabulary.DB_CHANGES.contains(call.name().stringValue())) {
                int others = 0;
                for (ClassDesc type : call.typeSymbol().parameterList()) {
                    others += sizeOf(type);
                }
                if (producer(at, others) instanceof Operand.Answer got
                        && got.call().owner().asInternalName().equals(COMPILATION)
                        && got.call().name().stringValue()
                                .equals(ModelVocabulary.STORE_ACCESSOR)) {
                    configuring.add(got.at());
                }
            }
        }
        for (int at = 0; at < flow.size(); at++) {
            switch (flow.get(at)) {
                case InvokeInstruction call -> {
                    boolean instance = call.opcode() != Opcode.INVOKESTATIC;
                    List<ClassDesc> stack = new ArrayList<>(call.typeSymbol().parameterList());
                    if (instance) {
                        stack.add(0, call.owner().asSymbol());
                    }
                    String target = call.owner().asInternalName();
                    String name = call.name().stringValue();
                    String callee = AMethod.of(target, name, call.type().stringValue());
                    if (target.equals(ANSWER) && name.equals("reports")
                            && throughLocals(producer(at, 0), 0) instanceof Operand.Answer asked
                            && asked.call().owner().asInternalName().equals(DB)
                            && asked.call().name().stringValue().equals("ask")) {
                        int arguments = 0;
                        for (ClassDesc type : asked.call().typeSymbol().parameterList()) {
                            arguments += sizeOf(type);
                        }
                        Operand store = producer(asked.at(), arguments);
                        Operand model = modelOfTheDb(store);
                        if (!(model instanceof Operand.Lost)) {
                            found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                    callee, -1, true, true, false, false, false, false, model,
                                    store, false, true));
                        }
                    }
                    int above = 0;
                    for (int i = stack.size() - 1; i >= 0; i--) {
                        ClassDesc type = stack.get(i);
                        if (type.descriptorString().equals(COMPILATION_TYPE)) {
                            boolean receiver = instance && i == 0;
                            if (name.equals("<init>") && !receiver && !isHelper(target, helper)) {
                                leaves(producer(at, above), at, null, -1);
                            }
                            boolean storeAccessor = receiver && target.equals(COMPILATION)
                                    && name.equals(ModelVocabulary.STORE_ACCESSOR);
                            boolean reads = receiver
                                    ? target.equals(COMPILATION) && !configuring.contains(at)
                                            && (storeAccessor
                                            || world.effects().readsReports(callee))
                                    : target.equals(REPORT)
                                            && name.equals(ModelVocabulary.ADEQUACY_REPORT_OF);
                            boolean report = reads && !storeAccessor;
                            boolean helping = !receiver && isHelper(target, helper);
                            boolean handsTheModelBack = call.typeSymbol().returnType()
                                    .descriptorString().equals(COMPILATION_TYPE);
                            boolean asks = helping && !name.equals(NOT_COMPILED)
                                    && handsTheModelBack;
                            boolean exempts = helping && name.equals(NOT_COMPILED)
                                    && world.exempt().contains(key);
                            boolean mutates = receiver && target.equals(COMPILATION)
                                    && world.effects().changes(callee);
                            boolean answers = (receiver && target.equals(COMPILATION)
                                    && ModelVocabulary.ANSWERS.contains(name))
                                    || (helping && !asks && !name.equals(NOT_COMPILED));
                            boolean strict = report && !(receiver
                                    && ModelVocabulary.SHOWS_ERRORS.contains(name));
                            found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                    callee, instance ? i - 1 : i, reads, report, asks, exempts,
                                    false, mutates, producer(at, above), new Operand.Nothing(),
                                    answers, strict));
                        } else if (type.descriptorString().equals(DB_TYPE)) {
                            boolean receiver = instance && i == 0;
                            Operand store = producer(at, above);
                            Operand model = modelOfTheDb(store);
                            if (receiver && target.equals(DB)) {
                                boolean changes = ModelVocabulary.DB_CHANGES.contains(name);
                                boolean readsReport = ModelVocabulary.DB_READS_A_REPORT
                                        .contains(name);
                                if (changes || readsReport) {
                                    found.computeIfAbsent(at, k -> new ArrayList<>())
                                            .add(new Site(at, callee, -1, readsReport, readsReport,
                                                    false, false, false, changes, model, store,
                                                    false, readsReport));
                                }
                            } else if (!receiver || !target.equals(DB)) {
                                found.computeIfAbsent(at, k -> new ArrayList<>())
                                        .add(new Site(at, callee, instance ? i - 1 : i, false,
                                                false, false, false, false, false, model, store,
                                                false, false));
                            }
                        } else if (type.descriptorString().startsWith("L")
                                || type.descriptorString().startsWith("[")) {
                            Operand handed = producer(at, above);
                            boolean model = leaves(handed, at, null, -1);
                            if (!model && handed instanceof Operand.Local
                                    && modelOfTheDb(handed) instanceof Operand.Local owner) {
                                // The store of a model is the model's to the one that is given it.
                                escapes.add(new Escape(owner, at, null, -1));
                                handed = owner;
                                model = true;
                            }
                            if (model && !inertWithAModel(target)
                                    && !(handed instanceof Operand.Answer)) {
                                // The model is handed on as something else, which is where a
                                // model goes through a generic method and comes back as itself.
                                // What runs there is not known by the types the call is written
                                // with, so it is taken to change the model.
                                found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                        callee, instance ? i - 1 : i, false, false, false, false,
                                        false, true, handed, new Operand.Nothing(), false,
                                        false));
                            }
                        }
                        above += sizeOf(type);
                    }
                }
                case FieldInstruction field when (field.opcode() == Opcode.PUTFIELD
                        || field.opcode() == Opcode.PUTSTATIC) -> {
                    String held = field.typeSymbol().descriptorString();
                    if (held.equals(COMPILATION_TYPE)) {
                        leaves(producer(at, 0), at, null, -1);
                    } else if (held.equals(DB_TYPE)) {
                        Operand model = modelOfTheDb(producer(at, 0));
                        if (model instanceof Operand.Local) {
                            escapes.add(new Escape(model, at, null, -1));
                        }
                    }
                }
                case ArrayStoreInstruction store when store.typeKind() == TypeKind.REFERENCE ->
                        leaves(producer(at, 0), at, null, -1);
                case StoreInstruction store when store.typeKind() == TypeKind.REFERENCE -> {
                    if (producer(at, 0) instanceof Operand.Field from
                            && modelFields.contains(from.key())) {
                        escapes.add(new Escape(new Operand.Local(store.slot()), at, null, -1));
                    }
                }
                case InvokeDynamicInstruction call -> {
                    String impl = lambdaImplementation(call);
                    if (impl != null) {
                        List<ClassDesc> stack = call.typeSymbol().parameterList();
                        int shift = lambdaTakesReceiver(call) ? 1 : 0;
                        creations.add(impl);
                        int above = 0;
                        for (int i = stack.size() - 1; i >= 0; i--) {
                            ClassDesc type = stack.get(i);
                            if (type.descriptorString().equals(DB_TYPE) && i >= shift) {
                                Operand store = producer(at, above);
                                found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                        impl, i - shift, false, false, false, false, true, false,
                                        modelOfTheDb(store), store, false, false));
                            }
                            if (type.descriptorString().equals(COMPILATION_TYPE)) {
                                Operand captured = producer(at, above);
                                leaves(captured, at, impl, i - shift);
                                if (i >= shift) {
                                    found.computeIfAbsent(at, k -> new ArrayList<>())
                                            .add(new Site(at, impl, i - shift, false, false, false,
                                                    false, true, false, captured,
                                                    new Operand.Nothing(), false, false));
                                } else if (world.effects().readsReports(impl)
                                        && !ModelVocabulary.SHOWS_ERRORS.contains(
                                        impl.substring(impl.indexOf('#') + 1,
                                                impl.indexOf('(')))) {
                                    found.computeIfAbsent(at, k -> new ArrayList<>())
                                            .add(new Site(at, impl, -1, true, true, false, false,
                                                    false, false, captured,
                                                    new Operand.Nothing(), false, true));
                                }
                            }
                            above += sizeOf(type);
                        }
                    }
                }
                default -> { }
            }
        }
        sites = found;
        return found;
    }

    /**
     * The model a store belongs to, where it was got from the model just now, and otherwise
     * nothing that can be placed, so that changing it is a change to whatever model there is.
     */
    private Operand modelOfTheDb(Operand db) {
        return modelOfTheDb(db, 0);
    }

    /**
     * What gave the value a variable holds, where the variable is given one value in one place and
     * is not an argument, and the variable itself otherwise.
     */
    private Operand throughLocals(Operand held, int depth) {
        if (depth < 8 && held instanceof Operand.Local local
                && storeCounts.getOrDefault(local.slot(), 0) == 1
                && !modelParameters.contains(local.slot())
                && !storeParameters.contains(local.slot())) {
            for (int at = 0; at < flow.size(); at++) {
                if (flow.get(at) instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE && store.slot() == local.slot()) {
                    return throughLocals(producer(at, 0), depth + 1);
                }
            }
        }
        return held;
    }

    /**
     * Followed through the store's own methods that return it, and through a variable that is
     * given one store once. A store made here with {@code new} belongs to no model, and says
     * {@link Operand.Nothing}.
     */
    private Operand modelOfTheDb(Operand db, int depth) {
        if (depth > 16) {
            return new Operand.Lost();
        }
        if (db instanceof Operand.Answer answer) {
            String owner = answer.call().owner().asInternalName();
            if (owner.equals(COMPILATION) && answer.call().name().stringValue()
                    .equals(ModelVocabulary.STORE_ACCESSOR)) {
                return producer(answer.at(), 0);
            }
            if (owner.equals(DB) && answer.call().typeSymbol().returnType().descriptorString()
                    .equals(DB_TYPE)) {
                int arguments = 0;
                for (ClassDesc parameter : answer.call().typeSymbol().parameterList()) {
                    arguments += sizeOf(parameter);
                }
                return modelOfTheDb(producer(answer.at(), arguments), depth + 1);
            }
            if (answer.call().typeSymbol().returnType().descriptorString().equals(DB_TYPE)
                    && world.analysed().contains(AMethod.of(owner,
                    answer.call().name().stringValue(), answer.call().type().stringValue()))) {
                // A method that is walked says what the model its store belongs to stands as, and
                // whether it answers only stores it made, which {@link #noModel} asks when it is
                // used: what it says is not known when the places a store is used are found.
                return answer;
            }
            return new Operand.Lost();
        }
        if (db instanceof Operand.FreshStore) {
            return new Operand.Nothing();
        }
        if (db instanceof Operand.Local local && storeParameters.contains(local.slot())
                && !stored.contains(local.slot())) {
            return db;
        }
        if (db instanceof Operand.Local local && storeCounts.getOrDefault(local.slot(), 0) == 1
                && !storeParameters.contains(local.slot())) {
            for (int at = 0; at < flow.size(); at++) {
                if (flow.get(at) instanceof StoreInstruction store
                        && store.typeKind() == TypeKind.REFERENCE
                        && store.slot() == local.slot()) {
                    return modelOfTheDb(producer(at, 0), depth + 1);
                }
            }
        }
        return new Operand.Lost();
    }

    private static DirectMethodHandleDesc lambdaHandle(InvokeDynamicInstruction call) {
        if (!call.bootstrapMethod().owner().descriptorString()
                .equals("Ljava/lang/invoke/LambdaMetafactory;")) {
            return null;
        }
        List<ConstantDesc> arguments = call.bootstrapArgs();
        return arguments.size() > 1 && arguments.get(1) instanceof DirectMethodHandleDesc handle
                ? handle : null;
    }

    static String lambdaImplementation(InvokeDynamicInstruction call) {
        DirectMethodHandleDesc handle = lambdaHandle(call);
        if (handle == null) {
            return null;
        }
        String owner = handle.owner().descriptorString();
        return AMethod.of(owner.substring(1, owner.length() - 1), handle.methodName(),
                handle.lookupDescriptor());
    }

    private static boolean lambdaTakesReceiver(InvokeDynamicInstruction call) {
        DirectMethodHandleDesc handle = lambdaHandle(call);
        return handle != null && switch (handle.kind()) {
            case VIRTUAL, INTERFACE_VIRTUAL, SPECIAL, INTERFACE_SPECIAL -> true;
            default -> false;
        };
    }

    private static int capturedArguments(InvokeDynamicInstruction call) {
        return call.typeSymbol().parameterList().size() - (lambdaTakesReceiver(call) ? 1 : 0);
    }

    /** Whether {@code owner} is the helper, or a class kept inside it. */
    static boolean isHelper(String owner, String helper) {
        return owner.equals(helper) || owner.startsWith(helper + "$");
    }

    private static String fieldKey(FieldInstruction field) {
        return field.owner().asInternalName() + "." + field.name().stringValue();
    }

    /**
     * What put the value {@code above} slots below the top of the stack there, before the
     * instruction at {@code at}. Instructions that move a value without being its source are
     * stepped back over, and what cannot be placed is lost.
     */
    private Operand producer(int at, int above) {
        long id = ((long) at << 16) | above;
        Operand held = producers.get(id);
        if (held == null) {
            held = producerComputed(at, above);
            producers.put(id, held);
        }
        return held;
    }

    private Operand producerComputed(int at, int above) {
        int need = above + 1;
        for (int i = at - 1; i >= 0; i--) {
            if (!(flow.get(i) instanceof Instruction instruction)) {
                return new Operand.Lost();
            }
            if (instruction instanceof TypeCheckInstruction check
                    && check.opcode() == Opcode.CHECKCAST) {
                continue;
            }
            if (instruction instanceof InvokeInstruction call
                    && call.owner().asInternalName().equals("java/util/Objects")
                    && call.name().stringValue().equals("requireNonNull")
                    && call.type().stringValue()
                            .equals("(Ljava/lang/Object;)Ljava/lang/Object;")) {
                continue;
            }
            if (instruction instanceof StackInstruction copy && copy.opcode() == Opcode.DUP
                    && need <= 2) {
                // The two on top are one value, so what put it there is what put the one under.
                need = 1;
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
                    case ConstantInstruction constant
                            when constant.opcode() == Opcode.ACONST_NULL ->
                            new Operand.Nothing();
                    case InvokeInstruction call -> new Operand.Answer(call, i);
                    case NewObjectInstruction made
                            when made.className().asInternalName().equals(DB) ->
                            new Operand.FreshStore();
                    case FieldInstruction field when field.opcode() == Opcode.GETFIELD
                            || field.opcode() == Opcode.GETSTATIC ->
                            new Operand.Field(fieldKey(field),
                                    field.opcode() == Opcode.GETSTATIC || onThis(i));
                    default -> new Operand.Lost();
                };
            }
            need = need - effect[1] + effect[0];
        }
        return new Operand.Lost();
    }

    /**
     * A place a model goes out of the variables the walk follows it by, into a lambda, a
     * constructor, a field, an array or a container, from which something else may change or read
     * it.
     *
     * @param impl  the lambda or method reference that captured it, where it is that, and null
     *              otherwise
     * @param index which argument of {@code impl} it is, and -1 for the receiver of a method
     *              reference
     */
    private record Escape(Operand operand, int at, String impl, int index) { }

    /**
     * Records that {@code held} goes out of the variables if it is a model, and says whether it is
     * one.
     */
    private boolean leaves(Operand held, int at, String impl, int index) {
        boolean model = switch (held) {
            case Operand.Local local -> holdsAModel(local.slot());
            case Operand.Field field -> modelFields.contains(field.key());
            case Operand.Answer made -> made.call().typeSymbol().returnType().descriptorString()
                    .equals(COMPILATION_TYPE);
            default -> false;
        };
        if (model) {
            escapes.add(new Escape(held, at, impl, index));
        }
        return model;
    }

    /**
     * The calls after a model went out of the variables that may change or read it there, as sites
     * of that model.
     *
     * <p>A call may change a model it is not handed when it can reach a change to one, or when it
     * runs what a lambda made here does and that lambda changes the model it is given or captured. A
     * call that runs a lambda made here that reads what a model found reads what a model that went
     * into a container is. What the call does is not known from the model it names, because the
     * model is somewhere else, so every model that went out and can still be reached is taken to
     * be changed or read, and the fields that hold a model are taken to be changed.
     */
    private Map<Integer, List<Site>> withEscapes(Map<Integer, List<Site>> base) {
        if (escapes.isEmpty() && modelFields.isEmpty()) {
            return base;
        }
        boolean armed = false;
        boolean readerArmed = false;
        for (String impl : creations) {
            armed |= world.effects().changes(impl) || facts.changingMethods().contains(impl);
            readerArmed |= (world.effects().readsReports(impl) && !ModelVocabulary.SHOWS_ERRORS
                    .contains(impl.substring(impl.indexOf('#') + 1, impl.indexOf('('))))
                    || (impl.startsWith(REPORT + "#") && impl.contains("#of("));
        }
        Map<Integer, List<Site>> out = new HashMap<>();
        base.forEach((at, here) -> out.put(at, new ArrayList<>(here)));
        for (int at = 0; at < flow.size(); at++) {
            if (!(flow.get(at) instanceof InvokeInstruction call)) {
                continue;
            }
            boolean runs = runsCode(call);
            boolean strikes = changesSomething(call) || (runs && armed);
            boolean looks = runs && readerArmed;
            if (!strikes && !looks) {
                continue;
            }
            for (Escape each : escapes) {
                boolean here = each.at() == at;
                if (!here && !reachableFrom(each.at())[at]) {
                    continue;
                }
                boolean captured = each.impl() != null;
                boolean capturedArmed = captured && (facts.changingMethods().contains(each.impl())
                        || (each.index() < 0 && world.effects().changes(each.impl())));
                if (!here && strikes && !(each.operand() instanceof Operand.Answer)
                        && (!captured || capturedArmed) && !alreadyChangedAt(each.operand(), at,
                        base)) {
                    out.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at, ESCAPE, -1,
                            false, false, false, false, false, true, each.operand(),
                            new Operand.Nothing(), false, false));
                }
                if (looks && !captured) {
                    out.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at, ESCAPE, -1,
                            true, true, false, false, false, false, each.operand(),
                            new Operand.Nothing(), false, true));
                }
            }
            if (strikes) {
                for (String field : modelFieldOrder) {
                    out.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at, ESCAPE, -1,
                            false, false, false, false, false, true, new Operand.Field(field, true),
                            new Operand.Nothing(), false, false));
                }
            }
        }
        return out;
    }

    private static final String ESCAPE = "<escape>#()V";

    /** Whether a site of the same model, already there at {@code at}, changes it. */
    private boolean alreadyChangedAt(Operand model, int at, Map<Integer, List<Site>> base) {
        if (!(model instanceof Operand.Local held)) {
            return false;
        }
        for (Site site : base.getOrDefault(at, List.of())) {
            if (site.operand() instanceof Operand.Local there && mutating(site)
                    && membersOf(there.slot()).contains(held.slot())) {
                return true;
            }
        }
        return false;
    }

    /** Whether the call may change a model it was not handed: it reaches a change to one. */
    private boolean changesSomething(InvokeInstruction call) {
        String callee = AMethod.of(call.owner().asInternalName(), call.name().stringValue(),
                call.type().stringValue());
        for (String target : world.effects().targets(callee)) {
            String owner = target.substring(0, target.indexOf('#'));
            if (!owner.equals(DB) && !isHelper(owner, world.helper())
                    && world.effects().changes(target)) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether the call runs what it is handed or what was made for it: the functional interfaces,
     * what runs a task, and any call that takes one.
     */
    private static boolean runsCode(InvokeInstruction call) {
        String owner = call.owner().asInternalName();
        if (owner.startsWith("java/util/function/") || owner.startsWith("java/util/concurrent/")
                || owner.equals("java/lang/Runnable")) {
            return true;
        }
        if (owner.startsWith("java/lang/reflect/") || owner.startsWith("java/lang/invoke/")) {
            return true;
        }
        if (!owner.startsWith("java/")) {
            return false;
        }
        String taken = call.type().stringValue();
        return taken.contains("Ljava/util/function/") || taken.contains("Ljava/lang/Runnable;")
                || taken.contains("Ljava/util/concurrent/Callable;")
                || taken.contains("Ljava/util/Comparator;");
    }

    /**
     * Whether a class of the platform or of the assertions only holds, compares or prints what it
     * is given as something else, and runs nothing of it. The ones that run what they are given,
     * the functional interfaces and what runs a task, are not, and neither is the repository's own
     * code.
     */
    private static boolean inertWithAModel(String owner) {
        boolean runs = owner.startsWith("java/util/function/")
                || owner.startsWith("java/util/concurrent/") || owner.equals("java/lang/Runnable")
                || owner.equals("java/lang/reflect/Method")
                || owner.equals("java/lang/invoke/MethodHandle");
        return !runs && (owner.startsWith("java/") || owner.startsWith("org/junit/"));
    }

    /** Whether the variable is given a model: it is an argument of that type or is made of one. */
    private boolean holdsAModel(int slot) {
        return holdsAModel(slot, new HashSet<>());
    }

    /**
     * Whether the variable may hold a model on some way through the method: it is an argument of
     * that type, or something it is given is a model, a copy of a variable that may hold one, or a
     * field that holds one.
     */
    private boolean holdsAModel(int slot, Set<Integer> seen) {
        if (modelParameters.contains(slot)) {
            return true;
        }
        if (!seen.add(slot)) {
            return false;
        }
        for (int at = 0; at < flow.size(); at++) {
            if (flow.get(at) instanceof StoreInstruction store
                    && store.typeKind() == TypeKind.REFERENCE && store.slot() == slot) {
                boolean model = switch (producer(at, 0)) {
                    case Operand.Answer made -> made.call().typeSymbol().returnType()
                            .descriptorString().equals(COMPILATION_TYPE);
                    case Operand.Local copy -> holdsAModel(copy.slot(), seen);
                    case Operand.Field field -> modelFields.contains(field.key());
                    default -> false;
                };
                if (model) {
                    return true;
                }
            }
        }
        return false;
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

    static int sizeOf(ClassDesc type) {
        return switch (type.descriptorString()) {
            case "V" -> 0;
            case "J", "D" -> 2;
            default -> 1;
        };
    }
}
