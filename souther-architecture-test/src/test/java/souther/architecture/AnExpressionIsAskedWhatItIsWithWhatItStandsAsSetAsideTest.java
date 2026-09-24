package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.compiler.core.Core;

import java.lang.classfile.Attributes;
import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeElement;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.Opcode;
import java.lang.classfile.attribute.PermittedSubclassesAttribute;
import java.lang.classfile.constantpool.ClassEntry;
import java.lang.classfile.instruction.ConstantInstruction;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.LoadInstruction;
import java.lang.classfile.instruction.NewObjectInstruction;
import java.lang.classfile.instruction.ReturnInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.lang.constant.DirectMethodHandleDesc;
import java.lang.reflect.AccessFlag;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What kind of expression a value is, is asked of the value with the type it stands as set aside.
 *
 * <p>A value the checker let stand as a wider type than its own is held under a {@link Core.Widen}
 * at the position it stands in, and nothing else about it changes: a read is still a read, a
 * construction a construction. So a reader asking which of those a value is, is asking about what
 * the {@code Widen} holds. Asked of the {@code Widen}, the answer is that the value is none of them,
 * and that answer is silent: an {@code instanceof} comes out false, a {@code switch} takes its
 * default, and the reading goes on as though the value were something it had no rule for.
 *
 * <p>So every test of a {@code Core} value's kind is one of three.
 *
 * <ul>
 *   <li>It asks of what {@link Core#withoutStanding} answered — through whatever names, copies and
 *       casts it went, and through any method whose every answer is such a value — or of a node
 *       built right there, which stands as nothing.</li>
 *   <li>It is a {@code switch} that names {@code Widen} among its cases, which is a reader saying
 *       what it does with one.</li>
 *   <li>It asks of the node a walk is standing at, where a {@code Widen} is a node like any other
 *       and goes the walk's own way down. Those are named below, one row per method, with how many
 *       such tests the method holds and why a {@code Widen} there is read as it should be.</li>
 * </ul>
 *
 * <p>A test that is none of them is red, and so is a row naming a method that holds a different
 * number of them. A cast is not counted: a cast of a {@code Widen} to anything else fails where it
 * stands, which is not the silence this is about.
 *
 * <p><b>Which values are set aside is followed, and not read off the method.</b> A method that calls
 * {@code withoutStanding} somewhere and tests something else says nothing about the test, so the
 * value tested is followed back to what made it ({@link WhereAValueOnTheStackCameFrom}).
 */
class AnExpressionIsAskedWhatItIsWithWhatItStandsAsSetAsideTest {

    private static final String CORE = "souther/compiler/core/Core";

    private static final String WIDEN = CORE + "$Widen";

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final CompiledOutputs EVERYTHING = CompiledOutputs.ofEverythingCompiledHere();

    /** One row: how many tests of the node a walk stands at a method holds, and why a
     *  {@code Widen} standing there is read as it should be. */
    private record Walk(int tests, String why) {}

    /**
     * Every method that tests the kind of the node a walk is standing at, how many such tests it
     * holds, and why a {@code Widen} standing there is read as it should be.
     */
    private static final Map<String, Walk> AT_THE_NODE_A_WALK_STANDS_AT = walks();

    @Test
    void everyTestOfAKindIsOfAValueWithItsStandingSetAside() {
        List<ClassModel> published = PUBLISHED.all();
        assertFalse(published.isEmpty(), "no class of this repository was read, so the rule is"
                + " asked of nothing");
        Map<String, Integer> found = unset(published);
        Map<String, Integer> named = new TreeMap<>();
        AT_THE_NODE_A_WALK_STANDS_AT.forEach((method, walk) -> named.put(method, walk.tests()));
        assertEquals(named, new TreeMap<>(found),
                "a test of what kind of expression a value is, asked of a value that may be standing"
                        + " as a wider type. Ask Core.withoutStanding(value), name Widen among the"
                        + " cases, or — where what is tested is the node a walk is standing at — say"
                        + " so in AT_THE_NODE_A_WALK_STANDS_AT, with why a Widen there is read as it"
                        + " should be");
    }

    /**
     * And that the reading tells the shapes apart, asked of the methods below, which are written the
     * ways a test of a kind is written.
     *
     * <p>The rule above passes where nothing is found, which is what a reading that followed nothing
     * would find too. What holds it to what javac writes is these: each is one shape, and which of
     * them come back is what the reading has to say.
     */
    @Test
    void theReadingTellsASetAsideValueFromOneThatIsNot() {
        ClassModel here = EVERYTHING.read(
                AnExpressionIsAskedWhatItIsWithWhatItStandsAsSetAsideTest.class.getName()
                        .replace('.', '/'));
        Map<String, Integer> expected = new TreeMap<>();
        expected.put(named(here, "bare"), 1);
        expected.put(named(here, "bareInAName"), 1);
        expected.put(named(here, "bareInASwitch"), 1);
        expected.put(named(here, "bareWithSeveralPatternsToACase"), 1);
        expected.put(named(here, "bareInALambda"), 1);
        expected.put(named(here, "setAsideOnOneWayOnly"), 1);
        assertEquals(expected, new TreeMap<>(unset(List.of(here))),
                "which of the shapes below test a value that may still be standing");
    }

    static boolean bare(Core e) {
        return e instanceof Core.Read;
    }

    static boolean setAside(Core e) {
        return Core.withoutStanding(e) instanceof Core.Read;
    }

    static boolean bareInAName(Core e) {
        Core held = e;
        return held instanceof Core.Read;
    }

    static boolean setAsideInAName(Core e) {
        Core held = Core.withoutStanding(e);
        return held instanceof Core.Read;
    }

    static boolean setAsideOnOneWayOnly(Core e, boolean which) {
        Core held = which ? Core.withoutStanding(e) : e;
        return held instanceof Core.Read;
    }

    static String bareInASwitch(Core e) {
        return switch (e) {
            case Core.Read r -> r.name();
            default -> "";
        };
    }

    static String setAsideInASwitch(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Read r -> r.name();
            default -> "";
        };
    }

    static String namingWidenInASwitch(Core e) {
        return switch (e) {
            case Core.Widen w -> namingWidenInASwitch(w.value());
            case Core.Read r -> r.name();
            default -> "";
        };
    }

    static String bareWithSeveralPatternsToACase(Core e) {
        return switch (e) {
            case Core.Int _, Core.Str _ -> "written";
            default -> "";
        };
    }

    static String namingWidenWithSeveralPatternsToACase(Core e) {
        return switch (e) {
            case Core.Widen w -> namingWidenWithSeveralPatternsToACase(w.value());
            case Core.Int _, Core.Str _ -> "written";
            default -> "";
        };
    }

    static boolean bareInALambda(List<Core> es) {
        return es.stream().anyMatch(e -> e instanceof Core.Read);
    }

    static boolean throughAHelperThatSetsItAside(Core e) {
        return aside(e) instanceof Core.Read;
    }

    private static Core aside(Core e) {
        Core bare = Core.withoutStanding(e);
        return bare;
    }

    static boolean ofANodeBuiltThere(Core.Binder name, Core e) {
        Core made = new Core.Read(name.name(), name.binding(), e.type(), e.pos());
        return made instanceof Core.Read;
    }

    /** The one method of this class named {@code name}. */
    private static String named(ClassModel owner, String name) {
        return owner.methods().stream()
                .filter(m -> m.methodName().equalsString(name))
                .map(m -> AMethod.of(owner, m))
                .findFirst().orElseThrow(() -> new AssertionError("no method " + name));
    }

    /**
     * Every method of {@code classes} holding a test of a kind that is not of a value with its
     * standing set aside and not a switch naming {@code Widen}, with how many it holds. A lambda's
     * are the method's it is written in.
     */
    private static Map<String, Integer> unset(List<ClassModel> classes) {
        Set<String> kinds = kinds();
        Set<String> settingAside = settingAside(classes, kinds);
        Map<String, Integer> out = new LinkedHashMap<>();
        for (ClassModel owner : classes) {
            Map<String, String> writtenIn = writtenIn(owner);
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                int count = unsetIn(method, kinds, settingAside);
                if (count > 0) {
                    out.merge(enclosing(AMethod.of(owner, method), writtenIn), count,
                            Integer::sum);
                }
            }
        }
        return out;
    }

    /** How many tests of a kind {@code method} holds that are of a value that may be standing. */
    private static int unsetIn(MethodModel method, Set<String> kinds, Set<String> settingAside) {
        WhereAValueOnTheStackCameFrom origins = null;
        List<CodeElement> elements = method.code().orElseThrow().elementList();
        Set<Integer> switchedOn = switchedOn(elements);
        int count = 0;
        for (int at = 0; at < elements.size(); at++) {
            boolean aSwitchs = isOf(elements, at, switchedOn);
            int depth;
            switch (elements.get(at)) {
                case TypeCheckInstruction check when check.opcode() == Opcode.INSTANCEOF
                        && kinds.contains(check.type().asInternalName()) && !aSwitchs -> depth = 0;
                case InvokeDynamicInstruction indy when isATypeSwitch(indy)
                        && labels(indy).stream().anyMatch(kinds::contains) -> {
                    if (labels(indy).contains(WIDEN)) {
                        continue;
                    }
                    // The number the switch starts looking from is above what it switches on.
                    depth = 1;
                }
                default -> {
                    continue;
                }
            }
            if (origins == null) {
                origins = WhereAValueOnTheStackCameFrom.of(method);
            }
            Set<WhereAValueOnTheStackCameFrom.Origin> from = origins.at(at, depth);
            List<CodeElement> code = origins.elements();
            if (from.isEmpty() || !from.stream().allMatch(
                    o -> standsAsNothing(o, code, kinds, settingAside))) {
                count++;
            }
        }
        return count;
    }

    /**
     * The names a type switch of {@code elements} reads what it switches on out of.
     *
     * <p>javac puts what a {@code switch} is over in a name of its own, reads it for the switch, and
     * reads it again where one case lists several patterns: those are tried one after another with
     * {@code instanceof} once the switch has picked the case. Such a test is the switch's, and is
     * counted as the switch is — a switch naming {@code Widen} has said what it does with one, and a
     * switch that does not is one test however many patterns a case of it lists.
     */
    private static Set<Integer> switchedOn(List<CodeElement> elements) {
        Set<Integer> out = new HashSet<>();
        for (int at = 0; at < elements.size(); at++) {
            if (elements.get(at) instanceof InvokeDynamicInstruction indy && isATypeSwitch(indy)) {
                // What is switched on is read just before the number it starts looking from.
                int loaded = previousInstruction(elements, previousInstruction(elements, at));
                if (loaded >= 0 && elements.get(loaded) instanceof LoadInstruction read) {
                    out.add(read.slot());
                }
            }
        }
        return out;
    }

    /** Whether the test at {@code at} is of a value read straight out of one of {@code names}. */
    private static boolean isOf(List<CodeElement> elements, int at, Set<Integer> names) {
        int loaded = previousInstruction(elements, at);
        return loaded >= 0 && elements.get(loaded) instanceof LoadInstruction read
                && names.contains(read.slot());
    }

    private static int previousInstruction(List<CodeElement> elements, int at) {
        for (int i = at - 1; i >= 0; i--) {
            if (elements.get(i) instanceof Instruction) {
                return i;
            }
        }
        return -1;
    }

    /** Whether the value {@code origin} made stands as nothing: a value set aside, a node built
     *  there, or no value at all. */
    private static boolean standsAsNothing(WhereAValueOnTheStackCameFrom.Origin origin,
                                           List<CodeElement> code, Set<String> kinds,
                                           Set<String> settingAside) {
        if (origin.isAParameter()) {
            return false;
        }
        return switch (code.get(origin.at())) {
            case InvokeInstruction call -> settingAside.contains(called(call));
            case NewObjectInstruction made -> kinds.contains(made.className().asInternalName());
            case ConstantInstruction nothing -> nothing.opcode() == Opcode.ACONST_NULL;
            default -> false;
        };
    }

    /**
     * The methods whose answer is a value with its standing set aside: {@link Core#withoutStanding}
     * and what a {@code Widen} holds, and every method answering a {@code Core} each of whose answers
     * is one of those or a node built there.
     *
     * <p>Every such method is taken to be one to begin with, and one is struck off where an answer
     * of it is anything else, until nothing more is struck off. Asked the other way round — none to
     * begin with, and one added where every answer is already known to be one — a method that
     * answers what it answers when it asks itself again would never be added, and a helper walking
     * down to the value it sets aside is exactly that.
     */
    private static Set<String> settingAside(List<ClassModel> classes, Set<String> kinds) {
        String answersCore = ")L" + CORE + ";";
        // What setting a value's standing aside is, and what a Widen holds: the two this is taken
        // from, which are what they are however they are written.
        Set<String> given = Set.of(
                AMethod.of(CORE, "withoutStanding", "(L" + CORE + ";" + answersCore),
                AMethod.of(WIDEN, "value", "(" + answersCore));
        Set<String> out = new HashSet<>(given);
        Map<String, MethodModel> candidates = new HashMap<>();
        for (ClassModel owner : classes) {
            for (MethodModel method : owner.methods()) {
                String key = AMethod.of(owner, method);
                if (!given.contains(key) && method.code().isPresent()
                        && method.methodTypeSymbol().descriptorString().endsWith(answersCore)) {
                    candidates.put(key, method);
                }
            }
        }
        out.addAll(candidates.keySet());
        boolean struck = true;
        while (struck) {
            struck = false;
            for (Map.Entry<String, MethodModel> each : candidates.entrySet()) {
                if (out.contains(each.getKey())
                        && !everyAnswerStandsAsNothing(each.getValue(), kinds, out)) {
                    out.remove(each.getKey());
                    struck = true;
                }
            }
        }
        return out;
    }

    private static boolean everyAnswerStandsAsNothing(MethodModel method, Set<String> kinds,
                                                      Set<String> settingAside) {
        List<CodeElement> elements = method.code().orElseThrow().elementList();
        WhereAValueOnTheStackCameFrom origins = null;
        boolean answers = false;
        for (int at = 0; at < elements.size(); at++) {
            if (!(elements.get(at) instanceof ReturnInstruction ret)
                    || ret.opcode() != Opcode.ARETURN) {
                continue;
            }
            if (origins == null) {
                origins = WhereAValueOnTheStackCameFrom.of(method);
            }
            for (WhereAValueOnTheStackCameFrom.Origin each : origins.at(at, 0)) {
                answers = true;
                if (!standsAsNothing(each, origins.elements(), kinds, settingAside)) {
                    return false;
                }
            }
        }
        return answers;
    }

    private static String called(InvokeInstruction call) {
        return AMethod.of(call.owner().asInternalName(), call.name().stringValue(),
                call.typeSymbol());
    }

    /** Whether {@code indy} is the switch javac writes for patterns over types. */
    private static boolean isATypeSwitch(InvokeDynamicInstruction indy) {
        DirectMethodHandleDesc bootstrap = indy.bootstrapMethod();
        return bootstrap.owner().descriptorString().equals("Ljava/lang/runtime/SwitchBootstraps;")
                && bootstrap.methodName().equals("typeSwitch");
    }

    /** The types a type switch has cases for. */
    private static List<String> labels(InvokeDynamicInstruction indy) {
        List<String> out = new ArrayList<>();
        for (ConstantDesc each : indy.bootstrapArgs()) {
            if (each instanceof ClassDesc type && type.isClassOrInterface()) {
                out.add(internalNameOf(type));
            }
        }
        return out;
    }

    private static String internalNameOf(ClassDesc type) {
        String descriptor = type.descriptorString();
        return descriptor.substring(1, descriptor.length() - 1);
    }

    /** The kinds of expression {@code Core} permits, but {@code Widen}. */
    private static Set<String> kinds() {
        ClassModel core = PUBLISHED.read(CORE);
        PermittedSubclassesAttribute permitted =
                core.findAttribute(Attributes.permittedSubclasses()).orElseThrow(
                        () -> new AssertionError(CORE + " permits nothing"));
        Set<String> out = new HashSet<>();
        for (ClassEntry each : permitted.permittedSubclasses()) {
            out.add(each.asInternalName());
        }
        if (!out.remove(WIDEN)) {
            throw new AssertionError(CORE + " no longer permits " + WIDEN
                    + ", so what this rule is about is not there");
        }
        return out;
    }

    /**
     * Which method each lambda of {@code owner} is written in: the method holding the instruction
     * that makes it. A lambda is the synthetic method a handle of that instruction names; a method
     * named by a method reference is not one, and is answered for as itself.
     */
    private static Map<String, String> writtenIn(ClassModel owner) {
        String self = owner.thisClass().asInternalName();
        Set<String> synthetic = new HashSet<>();
        for (MethodModel method : owner.methods()) {
            if (method.flags().has(AccessFlag.SYNTHETIC)) {
                synthetic.add(AMethod.of(owner, method));
            }
        }
        Map<String, String> out = new HashMap<>();
        for (MethodModel method : owner.methods()) {
            method.code().ifPresent(code -> code.elementList().forEach(element -> {
                if (!(element instanceof InvokeDynamicInstruction indy)) {
                    return;
                }
                for (ConstantDesc arg : indy.bootstrapArgs()) {
                    if (arg instanceof DirectMethodHandleDesc handle
                            && !FIELD_HANDLES.contains(handle.kind())
                            && internalNameOf(handle.owner()).equals(self)) {
                        String made = AMethod.of(self, handle.methodName(),
                                handle.lookupDescriptor());
                        if (synthetic.contains(made)) {
                            out.put(made, AMethod.of(owner, method));
                        }
                    }
                }
            }));
        }
        return out;
    }

    /** The handles that name a field rather than a method, which no lambda is. */
    private static final Set<DirectMethodHandleDesc.Kind> FIELD_HANDLES = Set.of(
            DirectMethodHandleDesc.Kind.GETTER, DirectMethodHandleDesc.Kind.SETTER,
            DirectMethodHandleDesc.Kind.STATIC_GETTER, DirectMethodHandleDesc.Kind.STATIC_SETTER);

    /** The method {@code method} is written in, through every lambda it is written in. */
    private static String enclosing(String method, Map<String, String> writtenIn) {
        String at = method;
        Set<String> met = new HashSet<>();
        while (writtenIn.containsKey(at) && met.add(at)) {
            at = writtenIn.get(at);
        }
        return at;
    }

    /** A walk over every node, which has no case for a {@code Widen} and goes on into what it holds,
     *  where the test meets the value. */
    private static final String GOES_ON_INTO_IT = "a walk over every node: a Widen has no case of"
            + " its own here and is walked on into what it holds, which is where the test meets the"
            + " value";

    /** A walk that counts the nodes a test picks out, and counts through a {@code Widen}. */
    private static final String COUNTS_THROUGH_IT = "counts the nodes of a tree the test picks out,"
            + " walking on through a Widen into what it holds";

    /** A rewrite that carries a {@code Widen} it does not replace through the slot operators. */
    private static final String REWRITES_UNDER_IT = "rewrites the node it stands at, and a Widen it"
            + " does not replace is carried through Core.mapChildren, which keeps what is rewritten"
            + " under it standing as what it stood as";

    /** Asked of the fork a walk stands at. */
    private static final String OF_A_FORK = "asked of a fork the walk is standing at, which is an"
            + " If, a Match or an attempt and never a Widen";

    /** Asked of the node the region walk stands at, which is past any {@code Widen}. */
    private static final String PAST_IT_ALREADY = "asked of the node InvariantChecker.walk stands"
            + " at, and that walk goes past a Widen to what it holds before it asks anything";

    private static Map<String, Walk> walks() {
        Map<String, Walk> out = new LinkedHashMap<>();
        String c = "souther/compiler/";
        String core = "L" + CORE + ";";
        row(out, c + "abort/AbortSites", "walk",
                "(" + core + "L" + c + "core/KernelContracts;Ljava/util/Set;"
                        + "Ljava/util/IdentityHashMap;)V", 1,
                "files each node's own answer and walks on through Core.forEachChild; a Widen"
                        + " answers nothing of its own, and what it holds is filed one step down");
        row(out, c + "check/AdmissibleReading", "gather",
                "(" + core + "Ljava/util/Set;L" + c + "check/Denotations;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "check/AnalysisBody", "visit",
                "(" + core + "L" + c + "check/ValueTemplates;Ljava/util/Set;Ljava/util/List;)V", 1,
                GOES_ON_INTO_IT);
        row(out, c + "check/Choice", "of", "(" + core + ")L" + c + "check/Choice;", 1,
                "what a choice is, asked of a node: a Widen is none, and the walks that open a"
                        + " choice find it one step down and replace it there, under the Widen");
        row(out, c + "check/Clauses", "readsOf", "(" + core + "Ljava/util/function/Consumer;)V", 1,
                COUNTS_THROUGH_IT);
        row(out, c + "check/Clauses", "substituted",
                "(" + core + "Ljava/util/Map;)" + core, 1, REWRITES_UNDER_IT);
        row(out, c + "check/Elaborator", "elaborating",
                "(L" + c + "ast/Hir$Expr;L" + c + "check/Scope;L" + c + "check/CheckContext;L" + c
                        + "types/Type;)" + core, 1,
                "asks what elaborating a construction answered, which is the construction itself:"
                        + " a value is not widened where it is made");
        row(out, c + "check/ElementBindings", "walk",
                "(" + core + "Ljava/util/Map;Ljava/util/Map;L" + c + "check/ElementProvenance;"
                        + "Ljava/util/Map;Ljava/util/Map;L" + c + "check/ValueTemplates;)V", 3,
                GOES_ON_INTO_IT);
        row(out, c + "check/InvariantChecker", "bindingIn",
                "(" + core + ")L" + CORE + "$LetIn;", 1, GOES_ON_INTO_IT);
        row(out, c + "check/InvariantChecker", "bindingInValueIn",
                "(" + core + ")L" + CORE + "$LetIn;", 1, PAST_IT_ALREADY);
        row(out, c + "check/InvariantChecker", "collectAlike",
                "(" + core + "L" + c + "check/Term;L" + c + "check/Denotations;Ljava/util/Set;)V",
                4, GOES_ON_INTO_IT);
        row(out, c + "check/InvariantChecker", "splitIn",
                "(" + core + ")L" + c + "check/InvariantChecker$SplitSite;", 4, GOES_ON_INTO_IT);
        row(out, c + "check/InvariantChecker", "splitValueIn",
                "(" + core + ")L" + c + "check/InvariantChecker$SplitSite;", 1, PAST_IT_ALREADY);
        row(out, c + "check/InvariantChecker", "walk",
                "(" + core + "L" + c + "check/Known;L" + c + "check/Denotations;L" + c
                        + "check/ContextMultiplicity;)L" + c + "check/Known;", 1,
                "the switch below the walk's own test for a Widen, which walks what one holds and"
                        + " returns before the switch is reached");
        row(out, c + "check/InvariantChecker", "without",
                "(" + core + "Ljava/util/Set;" + core + ")" + core, 3, REWRITES_UNDER_IT);
        row(out, c + "check/PathCompletion", "of",
                "(" + core + "L" + c + "check/Known;L" + c + "check/Denotations;)L" + c
                        + "check/Completion;", 1, PAST_IT_ALREADY);
        row(out, c + "check/PathCompletion", "operationAt", "(" + core + ")" + core, 1,
                PAST_IT_ALREADY);
        row(out, c + "check/PathEngine", "answeredHere",
                "(" + core + "L" + c + "check/Known;L" + c + "check/Denotations;)L" + c
                        + "check/Known;", 1, PAST_IT_ALREADY);
        row(out, c + "check/PathEngine", "isACheckedProducer", "(" + core + ")Z", 1,
                PAST_IT_ALREADY);
        row(out, c + "check/PathReachability", "unanswered",
                "(" + core + "L" + c + "coverage/CoverageSites$Plan;Ljava/util/Map;Ljava/util/Map;)"
                        + "Ljava/util/Optional;", 1, GOES_ON_INTO_IT);
        row(out, c + "check/PathReachability", "unreached",
                "(" + core + "L" + c + "check/Known;L" + c + "check/Denotations;L" + c
                        + "inputs/InputReads;Ljava/util/List;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "check/PathReachability", "walk",
                "(" + core + "L" + c + "check/Known;L" + c + "check/Denotations;L" + c
                        + "inputs/InputReads;Ljava/util/List;Z)V", 2, GOES_ON_INTO_IT);
        row(out, c + "check/Predicates", "chosenCalls",
                "(" + core + "L" + c + "check/Denotations;Ljava/util/Map;Ljava/util/Set;)V", 2,
                GOES_ON_INTO_IT);
        row(out, c + "check/Predicates", "names",
                "(" + core + "Ljava/util/Set;L" + c + "check/Denotations;)Z", 1, GOES_ON_INTO_IT);
        row(out, c + "check/StatedByClauses$Reading", "gather",
                "(" + core + "Ljava/util/Set;L" + c + "check/Denotations;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "claims/UnreachableClaims", "claimedUnder",
                "(" + core + "L" + c + "inputs/InputReads;L" + c + "check/Symbols;L" + c
                        + "check/DeclarationNewtypes;L" + c + "coverage/CoverageSites$Plan;L" + c
                        + "coverage/NormalReturn;ZLjava/util/List;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "claims/UnreachableReasons", "collect",
                "(" + core + "L" + c + "coverage/NormalReturn;Ljava/util/List;)V", 1,
                "follows what a node evaluates first to where a run stops, and what a Widen"
                        + " evaluates is what it holds (Evaluated)");
        row(out, c + "codegen/BodyGen", "genExpr",
                "(" + core + "L" + c + "types/Type;)L" + c + "types/Type;", 1,
                "asks whether the node just emitted was an unreachable, to say which shape it left;"
                        + " a Widen is emitted by its own case, as what it holds");
        row(out, c + "codegen/BodyGen", "walksInside", "(" + core + ")Z", 1, GOES_ON_INTO_IT);
        row(out, c + "core/GrowingFold", "adds", "(" + core + ")I", 2, COUNTS_THROUGH_IT);
        row(out, c + "core/GrowingFold", "aliased", "(" + core + "Ljava/util/Set;)I", 1,
                COUNTS_THROUGH_IT);
        row(out, c + "core/GrowingFold", "aliases",
                "(" + core + "L" + CORE + "$Binder;)Ljava/util/Set;", 1, COUNTS_THROUGH_IT);
        row(out, c + "core/GrowingFold", "appended", "(" + core + "Ljava/util/Set;)" + core, 1,
                "asked of an answering position answers() hands on, which has gone past a Widen"
                        + " to what it holds");
        row(out, c + "core/GrowingFold", "grownStep", "(" + core + ")" + core, 2,
                "asked of the step a fold is handed: a block, or the bindings a block captures, is"
                        + " handed as itself (Elaborator.answering widens what its body answers),"
                        + " and a function standing as another is not one this rewrites");
        row(out, c + "core/GrowingFold", "inserted", "(" + core + "Ljava/util/Set;)" + core, 1,
                "asked of an answering position answers() hands on, which has gone past a Widen"
                        + " to what it holds");
        row(out, c + "core/GrowingFold", "puttingStep", "(" + core + ")" + core, 2,
                "asked of the step a fold is handed: a block, or the bindings a block captures, is"
                        + " handed as itself (Elaborator.answering widens what its body answers),"
                        + " and a function standing as another is not one this rewrites");
        row(out, c + "core/GrowingFold", "reads", "(" + core + "Ljava/util/Set;)I", 1,
                COUNTS_THROUGH_IT);
        row(out, c + "core/GrowingFold", "rewrite",
                "(" + core + "L" + c + "types/ValueName$Stdlib$Operation;)" + core, 3,
                REWRITES_UNDER_IT);
        row(out, c + "core/GrowingFold", "uses", "(" + core + "L" + c + "types/BindingId;)I", 1,
                COUNTS_THROUGH_IT);
        row(out, c + "core/GrowingFold$Piped", "at", "(" + core + "Ljava/util/Set;)" + core, 1,
                "asked of an answering position answers() hands on, which has gone past a Widen"
                        + " to what it holds");
        row(out, c + "coverage/ComparisonCatalog", "occurrenceAt",
                "(" + core + ")Ljava/util/Optional;", 1,
                "whether the node a walk stands at is a comparison: a Widen is not, and the"
                        + " comparison under it is met one step down");
        row(out, c + "coverage/ComparisonCatalog", "walk",
                "(" + core + "Ljava/lang/String;Ljava/util/Map;Ljava/util/Map;)V", 2,
                GOES_ON_INTO_IT);
        row(out, c + "coverage/ComparisonEmissionIndex", "walk",
                "(" + core + "L" + c + "coverage/CoverageSites$Plan;Ljava/util/Map;)V", 1,
                GOES_ON_INTO_IT);
        row(out, c + "coverage/Methods", "collectCalls",
                "(" + core + "Ljava/util/Map;Ljava/util/Set;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "coverage/NodeAddresses", "binderSlots", "(" + core + ")V", 1,
                "which names a node binds, asked of every node the descent meets: a Widen binds"
                        + " none");
        row(out, c + "coverage/NormalReturn", "mayEnter", "(" + core + "I)Z", 1, OF_A_FORK);
        row(out, c + "partition/ComparisonAssessment", "readsAnswer",
                "(" + core + "L" + c + "types/BindingId;)Z", 1, COUNTS_THROUGH_IT);
        row(out, c + "partition/ComparisonReadings", "comparisonAt",
                "(" + core + ")L" + c + "check/Comparison;", 1,
                "whether the node the walk stands at is a comparison a source wrote: a Widen is"
                        + " not, and the comparison under it is met one step down");
        row(out, c + "partition/ComparisonReadings", "walk",
                "(" + core + "L" + c + "partition/ComparisonReadings$Body;L" + c
                        + "inputs/InputReads;L" + c + "partition/LiveFlow;Ljava/util/List;Z"
                        + "Ljava/util/List;Ljava/util/List;L" + c
                        + "partition/ConditionNumbering;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "partition/LiveFlow", "walk", "(" + core + "Ljava/util/Set;)V", 1,
                COUNTS_THROUGH_IT);
        row(out, c + "partition/PredicateReadings", "found",
                "(" + core + "Ljava/lang/String;L" + c + "inputs/InputReading;L" + c
                        + "inputs/InputReads;Ljava/util/List;L" + c
                        + "partition/RuleReachNumbering;)V", 1,
                "whether the node the walk stands at is a predicate a source wrote: a Widen is"
                        + " not, and the call under it is met one step down");
        row(out, c + "partition/PredicateReadings", "walk",
                "(" + core + "Ljava/lang/String;L" + c + "inputs/InputReading;L" + c
                        + "inputs/InputReads;L" + c + "partition/LiveFlow;ZLjava/util/List;L" + c
                        + "partition/RuleReachNumbering;Ljava/util/Set;L" + c
                        + "partition/PredicateReadings$Builds;)V", 1, GOES_ON_INTO_IT);
        row(out, c + "reading/CoverageRead", "walk",
                "(" + core + "L" + c + "reading/CoverageNaming;L" + c + "reading/Reach;Z)V", 1,
                GOES_ON_INTO_IT);
        row(out, c + "reading/Meetings", "meetingAt",
                "(" + core + "Ljava/util/Set;)Ljava/util/List;", 1,
                "whether values meet at the node the walk stands at: a Widen is one value standing"
                        + " as another, so none meet there");
        return out;
    }

    private static void row(Map<String, Walk> out, String owner, String name, String descriptor,
                            int tests, String why) {
        Walk already = out.put(AMethod.of(owner, name, descriptor), new Walk(tests, why));
        if (already != null) {
            throw new AssertionError(owner + "#" + name + descriptor + " is written down twice");
        }
    }
}
