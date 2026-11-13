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

    static final String COMPILATION = "souther/compiler/query/Compilation";

    static final String COMPILATION_TYPE = "L" + COMPILATION + ";";

    static final String REPORT = "souther/compiler/report/AdequacyReport";

    /** What a test calls on a model to read what is said of it. */
    private static final Set<String> READERS = Set.of("db", "adequacy", "warnings");

    /**
     * What changes a model once it has been asked about, so that what was asked is no longer what
     * it is: the sources it is made of and the way it is compiled.
     */
    private static final Set<String> MUTATORS = Set.of("update", "measure", "observe",
            "abandonWhen", "allowing", "withExampleBudget", "withJvmExampleDeadlines",
            "withEvaluationPolicy", "writtenOn", "withReadingPolicy", "withAdequacyPolicy");

    /** The helper's way of saying a model is read without being compiled. */
    private static final String NOT_COMPILED = "notCompiled";

    /** What marks a method the test engine runs, handing it what its parameters ask for. */
    private static final Set<String> RUN_BY_THE_ENGINE = Set.of(
            "Lorg/junit/jupiter/api/Test;", "Lorg/junit/jupiter/api/RepeatedTest;",
            "Lorg/junit/jupiter/api/TestFactory;", "Lorg/junit/jupiter/api/TestTemplate;",
            "Lorg/junit/jupiter/params/ParameterizedTest;", "Lorg/junit/jupiter/api/BeforeEach;",
            "Lorg/junit/jupiter/api/BeforeAll;", "Lorg/junit/jupiter/api/AfterEach;",
            "Lorg/junit/jupiter/api/AfterAll;");

    /** What a model keeps what it is compiled from in, and hands out. */
    private static final String DB = "souther/compiler/query/Db";

    /** What changes what a model is compiled from, through the store it hands out. */
    private static final Set<String> DB_MUTATORS = Set.of("set", "forget", "allowing");

    /**
     * What the walks of every method have found about the others so far.
     *
     * @param returns            what a method answers that was not one of its arguments
     * @param returnsParameter   the arguments a method answers, as {@code method#index}
     * @param readsParameter     the arguments a method reads what is said of before it asks about
     *                           them
     * @param readsReportParameter the arguments a method reads a report of, and not only what the
     *                           declarations say
     * @param asksParameter      the arguments a method asks about on every way through it
     * @param mutatesParameter   the arguments a method changes, or hands to what does
     * @param leavesAsked        the arguments a method leaves asked about on every way out, whatever
     *                           it did to them on the way
     * @param fields             what is written into each field of a model
     * @param fieldFlows         the fields an argument of a method is written into
     */
    record Facts(Map<String, ModelStanding> returns, Set<String> returnsParameter,
                 Set<String> readsParameter, Set<String> readsReportParameter,
                 Set<String> asksParameter, Set<String> mutatesParameter,
                 Set<String> leavesAsked, Map<String, ModelStanding> fields,
                 Map<String, Set<String>> fieldFlows) {

        static final Facts NONE = new Facts(Map.of(), Set.of(), Set.of(), Set.of(), Set.of(),
                Set.of(), Set.of(), Map.of(), Map.of());
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
     * @param readOnly  the code of the compiler, not walked, that is handed a model and leaves
     *                  what it is compiled from as it was
     */
    record World(String helper, Set<String> analysed, Set<String> written,
                 Map<String, Integer> captured, Set<String> exempt, Set<String> readOnly) { }

    /** What holds a model where it is used. */
    sealed interface Operand {

        /** A local variable. */
        record Local(int slot) implements Operand { }

        /** The answer of the call at {@code at}. */
        record Answer(InvokeInstruction call, int at) implements Operand { }

        /** A field. */
        record Field(String key) implements Operand { }

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
     */
    record Site(int at, String callee, int parameter, boolean readsDirectly, boolean report,
                boolean asksDirectly, boolean exempts, boolean creation, boolean mutates,
                Operand operand) { }

    /** What one walk found. */
    static final class Result {
        /** Reads of a model that was never asked about. */
        int unasked;
        /** Reads of a model whose origin could not be placed. */
        int lost;
        /** Reads of a model that was asked about, by this method. */
        int asked;
        ModelStanding returns = ModelStanding.ASKED;
        final Set<Integer> returnsParameter = new HashSet<>();
        final Set<Integer> readsParameter = new HashSet<>();
        final Set<Integer> readsReportParameter = new HashSet<>();
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
    private final Set<Integer> stored = new HashSet<>();
    private final Map<Integer, Integer> storeCounts = new HashMap<>();
    private Map<Integer, Set<Integer>> groups;
    private final Set<String> fieldsWritten = new HashSet<>();
    private final Map<String, Integer> capturedByLambdas = new HashMap<>();
    private final Map<Long, Operand> producers = new HashMap<>();
    private final boolean relevant;
    private final boolean engineRuns;
    private Map<Integer, List<Site>> sites;

    private Facts facts;
    private World world;
    private Map<Integer, Set<Integer>> asks;
    private Map<Integer, Set<Integer>> mutations;
    private Set<Integer> mutatesAnyAt;
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
            index++;
            slot += sizeOf(parameter);
        }
        boolean mentions = method.methodTypeSymbol().descriptorString().contains(COMPILATION_TYPE);
        for (CodeElement element : flow) {
            switch (element) {
                case StoreInstruction store when store.typeKind() == TypeKind.REFERENCE -> {
                    stored.add(store.slot());
                    storeCounts.merge(store.slot(), 1, Integer::sum);
                }
                case FieldInstruction field -> {
                    if (field.typeSymbol().descriptorString().equals(COMPILATION_TYPE)) {
                        mentions = true;
                        if (field.opcode() == Opcode.PUTFIELD || field.opcode() == Opcode.PUTSTATIC) {
                            fieldsWritten.add(fieldKey(field));
                        }
                    }
                }
                case InvokeInstruction call -> {
                    String name = call.owner().asInternalName();
                    mentions |= name.equals(COMPILATION) || name.equals(REPORT)
                            || isHelper(name, helper)
                            || call.type().stringValue().contains(COMPILATION_TYPE);
                }
                case InvokeDynamicInstruction call -> {
                    mentions |= call.type().stringValue().contains(COMPILATION_TYPE);
                    String impl = lambdaImplementation(call);
                    if (impl != null) {
                        capturedByLambdas.merge(impl, capturedArguments(call), Math::max);
                    }
                }
                default -> { }
            }
        }
        this.relevant = mentions;
        this.engineRuns = method.findAttribute(Attributes.runtimeVisibleAnnotations())
                .map(found -> found.annotations().stream().anyMatch(each ->
                        RUN_BY_THE_ENGINE.contains(each.classSymbol().descriptorString())))
                .orElse(false);
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
                handed.add(site.callee() + "#" + site.parameter());
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
        int size = flow.size();
        Map<Integer, List<Site>> all = sites(knownWorld.helper());
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
                    } else {
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
        List<Site> here = all.get(at);
        if (here == null) {
            return state;
        }
        Map<Integer, ModelStanding> out = null;
        for (Site site : here) {
            if (site.operand() instanceof Operand.Local local) {
                ModelStanding becomes = mutating(site) ? ModelStanding.UNASKED
                        : asking(site) ? ModelStanding.ASKED
                        : site.exempts() ? ModelStanding.EXEMPT : null;
                if (becomes != null) {
                    if (out == null) {
                        out = new HashMap<>(state);
                    }
                    for (int member : membersOf(local.slot())) {
                        out.put(member, becomes);
                    }
                }
            } else if (mutating(site)) {
                if (out == null) {
                    out = new HashMap<>(state);
                }
                out.replaceAll((slot, standing) -> ModelStanding.UNASKED);
            }
        }
        return out == null ? state : out;
    }

    /**
     * Whether the call changes the model it is handed, or may: it is a change to what the model is
     * compiled from, or it is handed to a method that changes it, or to code of the compiler that
     * is not walked and so is not known not to.
     */
    private boolean mutating(Site site) {
        if (facts.leavesAsked().contains(site.callee() + "#" + site.parameter())) {
            return false;
        }
        return site.mutates() || facts.mutatesParameter()
                .contains(site.callee() + "#" + site.parameter())
                || (escapes(site) && !world.readOnly().contains(site.callee()));
    }

    /** Whether the call hands the model to code of the compiler that is not walked. */
    private boolean escapes(Site site) {
        String owner = site.callee().substring(0, site.callee().indexOf('#'));
        return !site.creation() && owner.startsWith("souther/")
                && !owner.equals(COMPILATION) && !owner.equals(REPORT)
                && !isHelper(owner, world.helper()) && !world.analysed().contains(site.callee());
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
        String parameter = site.callee() + "#" + site.parameter();
        return !site.creation() && (site.asksDirectly()
                || facts.asksParameter().contains(parameter)
                || facts.leavesAsked().contains(parameter));
    }

    private boolean reading(Site site) {
        return site.readsDirectly()
                || facts.readsParameter().contains(site.callee() + "#" + site.parameter());
    }

    /** What the node at {@code at} does, now that the standing of everything before it is known. */
    private void account(int at, Map<Integer, List<Site>> all, Result result) {
        Map<Integer, ModelStanding> state = in.get(at);
        CodeElement element = flow.get(at);
        for (Site site : all.getOrDefault(at, List.of())) {
            for (String field : facts.fieldFlows()
                    .getOrDefault(site.callee() + "#" + site.parameter(), Set.of())) {
                result.fieldWrites.merge(field, standing(site.operand(), state),
                        ModelStanding::join);
            }
            if (reading(site)) {
                read(site.operand(), at, state, result, site.report() || facts
                        .readsReportParameter().contains(site.callee() + "#" + site.parameter()));
            }
            if (mutating(site) && site.operand() instanceof Operand.Local local) {
                for (int member : membersOf(local.slot())) {
                    if (modelParameters.contains(member) && !stored.contains(member)) {
                        result.mutatesParameter.add(parameterAt.get(member));
                    }
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
        if (operand instanceof Operand.Local local && modelParameters.contains(local.slot())
                && !stored.contains(local.slot())) {
            return parameterAt.get(local.slot());
        }
        return null;
    }

    private void read(Operand operand, int at, Map<Integer, ModelStanding> state, Result result,
                      boolean report) {
        ModelStanding standing = standing(operand, state);
        if (standing == ModelStanding.EXEMPT) {
            if (report) {
                result.unasked++;
            }
            return;
        }
        if (operand instanceof Operand.Local local) {
            boolean after = lookedAfter(local.slot())[at];
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
            case ASKED, EXEMPT -> { }
            case UNASKED -> result.unasked++;
            case HANDED_IN, LOST -> result.lost++;
        }
    }

    /** How the model {@code operand} holds stands, given the standing of the variables. */
    private ModelStanding standing(Operand operand, Map<Integer, ModelStanding> state) {
        return switch (operand) {
            case Operand.Lost _ -> ModelStanding.LOST;
            case Operand.Nothing _ -> ModelStanding.ASKED;
            case Operand.Field field -> field(field.key());
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

    private ModelStanding answered(Operand.Answer answer, Map<Integer, ModelStanding> state) {
        InvokeInstruction call = answer.call();
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
        if (!world.analysed().contains(method)) {
            return ModelStanding.LOST;
        }
        ModelStanding standing = facts.returns().getOrDefault(method, ModelStanding.ASKED);
        Map<Integer, ModelStanding> then = in.get(answer.at());
        for (Site site : sites(world.helper()).getOrDefault(answer.at(), List.of())) {
            if (facts.returnsParameter().contains(site.callee() + "#" + site.parameter())) {
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
                    value = true;
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
                    && DB_MUTATORS.contains(call.name().stringValue())) {
                int others = 0;
                for (ClassDesc type : call.typeSymbol().parameterList()) {
                    others += sizeOf(type);
                }
                if (producer(at, others) instanceof Operand.Answer got
                        && got.call().owner().asInternalName().equals(COMPILATION)
                        && got.call().name().stringValue().equals("db")) {
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
                    int above = 0;
                    for (int i = stack.size() - 1; i >= 0; i--) {
                        ClassDesc type = stack.get(i);
                        if (type.descriptorString().equals(COMPILATION_TYPE)) {
                            boolean receiver = instance && i == 0;
                            boolean reads = receiver
                                    ? target.equals(COMPILATION) && READERS.contains(name)
                                            && !configuring.contains(at)
                                    : target.equals(REPORT) && name.equals("of");
                            boolean report = reads && !(receiver && name.equals("db"));
                            boolean helping = !receiver && isHelper(target, helper);
                            boolean asks = helping && !name.equals(NOT_COMPILED);
                            boolean exempts = helping && name.equals(NOT_COMPILED)
                                    && world.exempt().contains(key);
                            boolean mutates = receiver && target.equals(COMPILATION)
                                    && MUTATORS.contains(name);
                            found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                    callee, instance ? i - 1 : i, reads, report, asks, exempts,
                                    false, mutates, producer(at, above)));
                        }
                        above += sizeOf(type);
                    }
                    if (instance && target.equals(DB) && DB_MUTATORS.contains(name)) {
                        found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                callee, -1, false, false, false, false, false, true,
                                modelOfTheDb(producer(at, above - 1))));
                    }
                }
                case InvokeDynamicInstruction call -> {
                    String impl = lambdaImplementation(call);
                    if (impl != null) {
                        List<ClassDesc> stack = call.typeSymbol().parameterList();
                        int shift = lambdaTakesReceiver(call) ? 1 : 0;
                        int above = 0;
                        for (int i = stack.size() - 1; i >= 0; i--) {
                            ClassDesc type = stack.get(i);
                            if (type.descriptorString().equals(COMPILATION_TYPE) && i >= shift) {
                                found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                        impl, i - shift, false, false, false, false, true, false,
                                        producer(at, above)));
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
        if (db instanceof Operand.Answer answer
                && answer.call().owner().asInternalName().equals(COMPILATION)
                && answer.call().name().stringValue().equals("db")) {
            return producer(answer.at(), 0);
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

    private static String lambdaImplementation(InvokeDynamicInstruction call) {
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
                    case FieldInstruction field when field.opcode() == Opcode.GETFIELD
                            || field.opcode() == Opcode.GETSTATIC ->
                            new Operand.Field(fieldKey(field));
                    default -> new Operand.Lost();
                };
            }
            need = need - effect[1] + effect[0];
        }
        return new Operand.Lost();
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
