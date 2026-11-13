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

    static final String COMPILATION = ModelVocabulary.COMPILATION;

    static final String COMPILATION_TYPE = ModelVocabulary.COMPILATION_TYPE;

    static final String REPORT = ModelVocabulary.REPORT;

    private static final String DB = ModelVocabulary.DB;

    private static final String DB_TYPE = ModelVocabulary.DB_TYPE;

    private static final String NOT_COMPILED = ModelVocabulary.NOT_COMPILED;

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
     */
    record Facts(Map<String, ModelStanding> returns, Set<String> returnsParameter,
                 Set<String> readsParameter, Set<String> readsReportParameter,
                 Set<String> readsStrictParameter, Set<String> asksParameter, Set<String> mutatesParameter,
                 Set<String> leavesAsked, Map<String, ModelStanding> fields,
                 Map<String, Set<String>> fieldFlows) {

        static final Facts NONE = new Facts(Map.of(), Set.of(), Set.of(), Set.of(), Set.of(),
                Set.of(),
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

        /** A field. */
        record Field(String key) implements Operand { }

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
                    } else if (!(site.operand() instanceof Operand.Nothing)) {
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
            if (site.operand() instanceof Operand.Nothing) {
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
            if (reading(site)) {
                read(site.operand(), at, state, result,
                        site.report() || anyTargetFact(facts.readsReportParameter(), site),
                        site.strict() || anyTargetFact(facts.readsStrictParameter(), site));
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
                } else if (site.operand() instanceof Operand.Field field) {
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
                    int above = 0;
                    for (int i = stack.size() - 1; i >= 0; i--) {
                        ClassDesc type = stack.get(i);
                        if (type.descriptorString().equals(COMPILATION_TYPE)) {
                            boolean receiver = instance && i == 0;
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
                                                    false, false));
                                }
                            } else if (!receiver || !target.equals(DB)) {
                                found.computeIfAbsent(at, k -> new ArrayList<>())
                                        .add(new Site(at, callee, instance ? i - 1 : i, false,
                                                false, false, false, false, false, model, store,
                                                false, false));
                            }
                        } else if ((type.descriptorString().startsWith("L")
                                || type.descriptorString().startsWith("["))
                                && !inertWithAModel(target)
                                && producer(at, above) instanceof Operand.Local held
                                && holdsAModel(held.slot())) {
                            // The model is handed on as something else, which is where a model
                            // goes through a generic method and comes back as itself. What runs
                            // there is not known by the types the call is written with, so it is
                            // taken to change the model.
                            found.computeIfAbsent(at, k -> new ArrayList<>()).add(new Site(at,
                                    callee, instance ? i - 1 : i, false, false, false, false,
                                    false, true, held, new Operand.Nothing(), false, false));
                        }
                        above += sizeOf(type);
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
                                        producer(at, above), new Operand.Nothing(), false,
                                        false));
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
            return new Operand.Lost();
        }
        if (db instanceof Operand.FreshStore) {
            return new Operand.Nothing();
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
            int[] effect = effect(instruction);
            if (effect == null) {
                return new Operand.Lost();
            }
            if (need <= effect[1]) {
                int found = i;
                return switch (instruction) {
                    case LoadInstruction load when load.typeKind() == TypeKind.REFERENCE ->
                            new Operand.Local(load.slot());
                    case ConstantInstruction constant
                            when constant.opcode() == Opcode.ACONST_NULL ->
                            new Operand.Nothing();
                    case InvokeInstruction call -> new Operand.Answer(call, i);
                    case StackInstruction dup when dup.opcode() == Opcode.DUP
                            && madeADbBefore(found) -> new Operand.FreshStore();
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
        if (modelParameters.contains(slot)) {
            return true;
        }
        for (int at = 0; at < flow.size(); at++) {
            if (flow.get(at) instanceof StoreInstruction store
                    && store.typeKind() == TypeKind.REFERENCE && store.slot() == slot
                    && producer(at, 0) instanceof Operand.Answer made
                    && made.call().typeSymbol().returnType().descriptorString()
                            .equals(COMPILATION_TYPE)) {
                return true;
            }
        }
        return false;
    }

    private boolean madeADbBefore(int at) {
        return at > 0 && flow.get(at - 1) instanceof NewObjectInstruction made
                && made.className().asInternalName().equals(DB);
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
