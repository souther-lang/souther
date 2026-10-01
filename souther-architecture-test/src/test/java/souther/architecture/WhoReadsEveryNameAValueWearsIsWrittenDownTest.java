package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.CodeModel;
import java.lang.classfile.Instruction;
import java.lang.classfile.MethodModel;
import java.lang.classfile.constantpool.LoadableConstantEntry;
import java.lang.classfile.constantpool.MemberRefEntry;
import java.lang.classfile.constantpool.MethodHandleEntry;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which methods take every name off a value one at a time.
 *
 * <p>Three ways do it: the walk itself ({@code TypeOps#newtypeSpine}), the names it took off
 * ({@code TypeOps#newtypeChain}), and a position read whole ({@code TypeView#of}). Each asks what
 * every name wraps, so over a chain of names each costs the chain — and a reader that wanted only
 * what is under the names, or only whether one is worn, pays that for an answer the compilation
 * already holds ({@code NewtypeInners#terminal}) or a step that is one name long
 * ({@code TypeOps#outermost}).
 *
 * <p>So the readers that do walk are written down. What entitles one is that it uses the names
 * themselves — puts them back on, reads the rules written at each, reports one — or that it is
 * code generation, whose reads of the declarations under a name are what its classes are recorded
 * as built against. A reader that wants the shape alone reads {@code TypeView#shapeOf}, and a
 * reader that wants the base reads {@code TypeOps#base}.
 *
 * <p>Read off the compiled classes, per method and per overload ({@link AMethod}), and a method
 * handed over to be called later is a caller. The rows are named rather than counted: a walk that
 * read no instructions comes back with nothing, which is not what this expects.
 */
class WhoReadsEveryNameAValueWearsIsWrittenDownTest {

    private static final String CHECK = "souther/compiler/check/";

    private static final String TYPE_OPS = CHECK + "TypeOps";

    private static final String TYPE_VIEW = CHECK + "TypeView";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    private static final String INPUTS = "souther/compiler/inputs/";

    private static final String PARTITION = "souther/compiler/partition/";

    private static final String TYPE = "Lsouther/compiler/types/Type;";

    private static final String INNERS = "L" + CHECK + "NewtypeInners;";

    private static final String SYMBOLS = "L" + CHECK + "Symbols;";

    private static final String PUBLISHED = "L" + CHECK + "PublishedDeclarations;";

    private static final String CONTEXT = "L" + CHECK + "RuleReadingContext;";

    private static final String SOURCE = "L" + CHECK + "RuleReadingSource;";

    private static final String BOUNDS = "Lsouther/compiler/numeric/NumericDomain$Bounds;";

    private static final String HELD = "L" + CHECK + "FieldDomains$Held;";

    private static final String REALIZATION = "L" + PARTITION + "TermRealizations$Realization;";

    private static final String THE_SPINE = TYPE_OPS + "#newtypeSpine";

    private static final String THE_NAMES = TYPE_OPS + "#newtypeChain";

    private static final String THE_POSITION = TYPE_VIEW + "#of";

    /**
     * Every method that walks, and the way it walks by.
     *
     * <p>The walk and what is made of it: the names it took off, a position read whole, the
     * position read off the declarations, and the terminal of a capability that does not hold it
     * whole — which is that capability walking, and is answered once per module where the
     * compilation answers it.
     *
     * <p>Code generation: the order a sort hands its values over in is read from every name, which
     * is what the classes it emits are recorded as built against.
     *
     * <p>A reading of the rules on each name: a value is read at the path each name it wears is
     * worn under.
     *
     * <p>Readers of a position that put its names back on a value they build, read the rules
     * written at each name, or tell what a value is written under: every one of them reads
     * {@code TypeView#wrappers} whole, directly or through what it hands the position to.
     */
    private static final List<String> WALKING = List.of(
            row(CHECK + "InvariantChecker", "name",
                    "(Lsouther/compiler/core/Core;L" + CHECK + "RuleKey;" + TYPE + "L" + CHECK
                            + "Denotations;" + SYMBOLS
                            + "ILjava/util/Map;Ljava/util/Map;Ljava/util/Map;Ljava/util/Map;)V",
                    THE_NAMES),
            row(CHECK + "NewtypeInners", "terminal", "(" + TYPE + ")" + TYPE, THE_SPINE),
            row(CHECK + "Ordering", "held",
                    "(" + TYPE + "Lsouther/compiler/core/Core$OrderingBasis;" + INNERS + ")L"
                            + CHECK + "Ordering;",
                    THE_SPINE),
            row(TYPE_OPS, "newtypeChain", "(" + TYPE + INNERS + ")Ljava/util/List;", THE_SPINE),
            row(TYPE_VIEW, "asWritten", "(" + TYPE + SYMBOLS + PUBLISHED + ")L" + TYPE_VIEW + ";",
                    THE_POSITION),
            row(TYPE_VIEW, "of", "(" + TYPE + INNERS + SYMBOLS + PUBLISHED + ")L" + TYPE_VIEW + ";",
                    THE_SPINE),
            row(INPUTS + "InputDomain", "walk",
                    "(L" + INPUTS + "TermPath;" + TYPE + "L" + INPUTS + "ExpansionTrace;" + CONTEXT
                            + "L" + INPUTS + "PlacedRules;Ljava/util/List;Ljava/util/List;"
                            + "Ljava/util/Set;L" + INPUTS + "RuleHandoffs;L" + INPUTS
                            + "NameReach$Observed;L" + INPUTS + "InputDomain$Gathered;L" + INPUTS
                            + "InputDomain$Reach;)V",
                    THE_POSITION),
            row(PARTITION + "BehaviorInputs$Standing", "step",
                    "(L" + INPUTS + "TermPath$Step;" + INNERS + SYMBOLS + PUBLISHED
                            + "Ljava/util/List;)Z",
                    THE_POSITION),
            row(PARTITION + "ConstructionPlan", "applying",
                    "(L" + PARTITION + "ConstructionPlan$Settled;L" + INPUTS + "Refinement;" + INNERS
                            + SYMBOLS + PUBLISHED + ")L" + PARTITION + "ConstructionPlan$Settled;",
                    THE_POSITION),
            row(PARTITION + "ConstructionPlan", "node",
                    "(" + TYPE + "L" + INPUTS + "TermPath;" + INNERS + SYMBOLS + PUBLISHED
                            + "ILjava/util/Set;L" + INPUTS + "Requirements;L" + PARTITION
                            + "ConstructionPlan$HowManyItHolds;)L" + PARTITION
                            + "ConstructionPlan$NodeResult;",
                    THE_POSITION),
            row(PARTITION + "ContainersAddingUp", "to",
                    "(Lsouther/compiler/numeric/Place;" + TYPE + "L" + INPUTS + "TermOrders;L"
                            + INPUTS + "SearchRegion;" + CONTEXT + "L" + PARTITION
                            + "ContainersAddingUp$HowManyIsAskedFor;)" + REALIZATION,
                    THE_POSITION),
            row(PARTITION + "PartitionClasses", "of",
                    "(" + TYPE + CONTEXT + "Ljava/util/Set;)Ljava/util/List;", THE_POSITION),
            row(PARTITION + "Partitions", "admittedStrings",
                    "(" + TYPE + CONTEXT + "I)Ljava/util/List;", THE_POSITION),
            row(PARTITION + "Partitions", "displacedRepresentativesOf",
                    "(" + TYPE + CONTEXT + BOUNDS + HELD + ")Ljava/util/List;", THE_POSITION),
            row(PARTITION + "Partitions", "inReserve",
                    "(" + TYPE + CONTEXT + BOUNDS + ")Ljava/util/List;", THE_POSITION),
            row(PARTITION + "Partitions", "measureAt",
                    "(Ljava/util/List;L" + PARTITION + "PositionMeasurements;L" + PARTITION
                            + "Axis;L" + INPUTS + "NumericTerm$FromOnePosition;Ljava/util/List;"
                            + "Ljava/util/List;L" + INPUTS + "Quantities;" + CONTEXT
                            + "Lsouther/compiler/values/Allowance;L" + INPUTS + "RulesWithNoLine;L"
                            + INPUTS + "RulesWithNoLine$Gathered;L" + PARTITION
                            + "EvidenceAccount;)L" + PARTITION + "BodyCutInspection;",
                    THE_POSITION),
            row(PARTITION + "Partitions", "notBuilt",
                    "(" + TYPE + CONTEXT + HELD + ")Ljava/util/Set;", THE_POSITION),
            row(PARTITION + "Partitions", "notOffered",
                    "(" + TYPE + CONTEXT + ")L" + PARTITION + "StringOfferShortfall;",
                    THE_POSITION),
            row(PARTITION + "Partitions", "representativesHolding",
                    "(" + TYPE + CONTEXT + BOUNDS + HELD + "Ljava/util/Set;)Ljava/util/List;",
                    THE_POSITION),
            row(PARTITION + "Partitions", "representativesOf",
                    "(" + TYPE + CONTEXT + BOUNDS + "Ljava/util/Set;)Ljava/util/List;",
                    THE_POSITION),
            row(PARTITION + "TermRealizations", "atThoseParts",
                    "(Ljava/util/Map;" + TYPE + "L" + CHECK + "Carrier;" + SOURCE + ")"
                            + REALIZATION,
                    THE_POSITION),
            row(PARTITION + "TermRealizations", "holdingExactly",
                    "(" + TYPE + "Lsouther/compiler/numeric/Place;" + CONTEXT + ")" + REALIZATION,
                    THE_POSITION),
            row(PARTITION + "TermRealizations", "namesOf",
                    "(" + TYPE + SOURCE + ")L" + PARTITION + "WornNames;", THE_POSITION),
            row(PARTITION + "TermRealizations", "onThoseParts",
                    "(Ljava/util/Map;" + TYPE + "L" + CHECK + "Carrier;" + SOURCE + ")"
                            + REALIZATION,
                    THE_POSITION),
            row(PARTITION + "TermRealizations", "oneValue",
                    "(L" + PARTITION + "FixtureTemplate;" + TYPE + SOURCE + ")" + REALIZATION,
                    THE_POSITION),
            row(PARTITION + "ValuesCarryingANumber", "at",
                    "(L" + PARTITION + "ConstructionPlan$Slot;)L" + PARTITION + "FixtureTemplate;",
                    THE_POSITION),
            row(PARTITION + "Witnesses", "varied",
                    "(" + TYPE + "I" + CONTEXT + ")L" + PARTITION + "FixtureTemplate;",
                    THE_POSITION));

    private static String row(String owner, String name, String descriptor, String way) {
        return AMethod.of(owner, name, descriptor) + " -> " + way;
    }

    @Test
    void everyMethodThatTakesEveryNameOffIsWrittenDown() {
        Set<String> found = walking();
        assertEquals(WALKING, List.copyOf(found),
                () -> "the methods that take every name off a value are not the ones written"
                        + " down.\n  found:\n    " + String.join("\n    ", found)
                        + "\nTake the terminal (NewtypeInners#terminal), the shape"
                        + " (TypeView#shapeOf) or the outermost name (TypeOps#outermost), or say"
                        + " here why this method reads every name.");
    }

    private static Set<String> walking() {
        Set<String> found = new TreeSet<>();
        for (ClassModel model : COMPILED.all()) {
            for (MethodModel method : model.methods()) {
                for (Instruction instruction : instructionsOf(method)) {
                    walkedBy(instruction).ifPresent(way -> found.add(
                            AMethod.of(model, method) + " -> " + way));
                }
            }
        }
        return found;
    }

    /** The way an instruction walks, if it names one: by calling it, or by handing it over. */
    private static Optional<String> walkedBy(Instruction instruction) {
        return switch (instruction) {
            case InvokeInstruction call -> aWayToWalk(call.owner().name().stringValue(),
                    call.name().stringValue());
            case InvokeDynamicInstruction handed -> {
                for (LoadableConstantEntry each : handed.invokedynamic().bootstrap().arguments()) {
                    if (each instanceof MethodHandleEntry handle) {
                        MemberRefEntry member = handle.reference();
                        Optional<String> way = aWayToWalk(member.owner().name().stringValue(),
                                member.name().stringValue());
                        if (way.isPresent()) {
                            yield way;
                        }
                    }
                }
                yield Optional.empty();
            }
            default -> Optional.empty();
        };
    }

    private static Optional<String> aWayToWalk(String owner, String name) {
        boolean theWalk = TYPE_OPS.equals(owner)
                && (name.equals("newtypeSpine") || name.equals("newtypeChain"));
        boolean aPositionReadWhole = TYPE_VIEW.equals(owner) && name.equals("of");
        return theWalk || aPositionReadWhole ? Optional.of(owner + "#" + name) : Optional.empty();
    }

    private static List<Instruction> instructionsOf(MethodModel method) {
        Optional<CodeModel> code = method.code();
        return code.map(each -> each.elementList().stream()
                .filter(Instruction.class::isInstance)
                .map(Instruction.class::cast)
                .toList()).orElse(List.of());
    }
}
