package souther.architecture;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.constant.DirectMethodHandleDesc;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every method that holds what one reader handed over, including the ones it was handed on to.
 *
 * <p><b>A rule about a value is not a rule about the method that asked for it.</b> A method that
 * asks a block for its positions and takes the first of them is one reader; the same method written
 * as {@code first(block.members())} is two, and nothing about the second is different except where
 * the line was cut. Asked of one method at a time, a rule saying no reader takes a position by where
 * it is stops holding the moment somebody extracts a helper — and extracting a helper is what
 * happens to a walk that is written twice.
 *
 * <p>So the subject is what the value reaches. A method holds the value if it asked for it, or if a
 * method that holds it calls it and it has somewhere to put it — which is what a parameter of a
 * type a walk can be handed is.
 *
 * <p><b>Wider than the value, and that is the safe direction.</b> Which argument of a call a value
 * lands in is not read here, so a method that takes a walk of something else from a caller that
 * happens to hold one of these is a method this says holds it. A rule written on top of this is
 * therefore asked of more methods than strictly hold the value, and a rule that comes back with
 * nobody has said something about all of them — which is the direction a guard is worth having in.
 * The other way round, a guard that under-reaches is one that passes while the thing it is about
 * goes on happening somewhere it did not look.
 *
 * <p>Method references are calls. A walk handed to {@code this::something} arrives there as surely
 * as one handed over by name, and the name is in the handle the call site was built with.
 *
 * <p><b>And it stops where the order does.</b> A walk handed to something that sorts it, or that
 * answers with the one element a collection was proved to hold, does not arrive on the other side in
 * the order it left in — so what happens there is about the order that place decided and not about
 * the one the value never had. Those places are named below, few, and each of them says at its own
 * boundary what it promises. Followed through one of them, this rule would report the sort's own
 * reading of its own output, which is the reading that makes an order the value's rather than the
 * walk's.
 */
final class WhoHoldsWhatAReaderHandedOver {

    /**
     * Where a walk stops being the walk it arrived as.
     *
     * <p>Each of these answers in an order it decided: the one element a collection holds, the
     * order a name gives, the order an atom domain gives. Whether each of them keeps that promise is
     * its own to say and is said where it is written — {@code TheOnly} refuses a collection that is
     * not of one, {@code PlanOrder} refuses a key that fails to tell two unequal items apart, and
     * {@code CanonicalForm#entriesIn} refuses two positions an order cannot tell apart. This is a
     * list of promises and not of exemptions, which is why it is checked against what exists
     * ({@link #boundariesThatAreNotThere}).
     */
    static final Set<String> WHERE_A_WALK_STOPS = Set.of(
            "souther/compiler/values/TheOnly#of",
            "souther/compiler/values/InOneOrder#of",
            "souther/compiler/values/PlanOrder#inOrder",
            "souther/compiler/values/PlanOrder#canonical",
            "souther/compiler/numeric/CanonicalForm#entriesIn",
            "souther/compiler/numeric/CanonicalForm#atomsIn",
            "souther/compiler/inputs/NumericTerms#inOrder",
            "souther/compiler/inputs/NumericTerms#entriesInOrder");

    /**
     * The types a walk of something arrives in.
     *
     * <p>What makes a parameter somewhere a collection can be put. A method taking none of these
     * cannot have been handed one, whoever called it — so the walk stops there rather than running
     * on through every method the caller reaches.
     */
    private static final Set<String> A_WALK_ARRIVES_IN = Set.of(
            "java/util/Collection", "java/util/List", "java/util/Set", "java/util/Map",
            "java/util/SequencedCollection", "java/util/SequencedSet", "java/util/SequencedMap",
            "java/util/SortedSet", "java/util/SortedMap", "java/util/NavigableSet",
            "java/lang/Iterable", "java/util/Iterator", "java/util/stream/Stream",
            "java/util/stream/BaseStream");

    private final Map<String, MethodModel> byName = new HashMap<>();
    private final Map<String, Set<String>> calls = new HashMap<>();
    private final Set<String> canBeHandedAWalk = new HashSet<>();

    /** Every method compiled in {@code where}, with what each of them calls. */
    WhoHoldsWhatAReaderHandedOver(CompiledOutputs where) {
        for (ClassModel read : where.all()) {
            String owner = read.thisClass().name().stringValue();
            for (MethodModel each : read.methods()) {
                String name = owner + "#" + each.methodName().stringValue();
                byName.put(name, each);
                calls.computeIfAbsent(name, _ -> new HashSet<>()).addAll(calledBy(each));
                if (hasSomewhereToPutAWalk(each)) {
                    canBeHandedAWalk.add(name);
                }
            }
        }
    }

    /**
     * Every method holding what {@code owner#member} hands over.
     *
     * <p>The ones that ask for it, and then every method one of those calls that a walk can arrive
     * in, until nothing more is reached.
     */
    Set<String> holdingWhat(String owner, String member) {
        Set<String> holding = new HashSet<>();
        Deque<String> toFollow = new ArrayDeque<>();
        byName.forEach((name, method) -> {
            if (asks(method, owner, member)) {
                holding.add(name);
                toFollow.add(name);
            }
        });
        while (!toFollow.isEmpty()) {
            for (String called : calls.getOrDefault(toFollow.remove(), Set.of())) {
                if (canBeHandedAWalk.contains(called) && !WHERE_A_WALK_STOPS.contains(called)
                        && holding.add(called)) {
                    toFollow.add(called);
                }
            }
        }
        return holding;
    }

    /** The method this name is of, for a rule that reads what it does. */
    MethodModel methodNamed(String name) {
        return byName.get(name);
    }

    /**
     * What takes something out of a walk by where it is rather than by what it is.
     *
     * <p>Named by what is called and not by where the call goes, since a method that does one of
     * these while holding a walk has the order in its answer whatever it does next.
     *
     * <p>A walk itself is not one of them. Every {@code for (each : these)} compiles to an iterator
     * and a question about what is next, so a rule naming {@code next} would name every reader that
     * walks anything at all — what tells the two apart is what stands between them, and a reader
     * taking the first asks for it straight away ({@link #asksAWalkForItsFirstAndNothingElse}).
     */
    private static final Set<String> BY_WHERE_IT_IS = Set.of(
            "getFirst", "getLast", "findFirst", "indexOf", "lastIndexOf",
            "limit", "skip", "reduce", "toArray", "listIterator",
            "firstKey", "lastKey", "firstEntry", "lastEntry", "first", "last");

    /**
     * Whether this method takes something out of a walk by where it is.
     *
     * <p>Asked of what the method calls and not of what the walk it holds reaches. A method with
     * one of these in it either does it to what it was handed, which is the defect, or does it to
     * something else while holding a walk, which is a method doing two things and is worth being
     * told about either way.
     */
    static boolean takesSomethingByWhereItIs(MethodModel method) {
        List<InvokeInstruction> made = method.code().stream()
                .flatMap(code -> code.elementStream())
                .filter(InvokeInstruction.class::isInstance)
                .map(InvokeInstruction.class::cast)
                .toList();
        return made.stream().anyMatch(call -> BY_WHERE_IT_IS.contains(call.name().stringValue())
                        || isReadingAListByIndex(call))
                || asksAWalkForItsFirstAndNothingElse(made);
    }

    /** {@code get} of a list or of an iterator's place, which a map is asked the same word. */
    private static boolean isReadingAListByIndex(InvokeInstruction call) {
        return call.name().stringValue().equals("get")
                && (call.owner().asInternalName().equals("java/util/List")
                        || call.owner().asInternalName().equals("java/util/ArrayList"));
    }

    /** A walk asked for its first and nothing else, which is the same read written the long way:
     *  a walk asks whether there is a next one first, and this asks for it straight away. */
    private static boolean asksAWalkForItsFirstAndNothingElse(List<InvokeInstruction> made) {
        for (int at = 0; at + 1 < made.size(); at++) {
            if (made.get(at).name().stringValue().equals("iterator")
                    && made.get(at + 1).name().stringValue().equals("next")) {
                return true;
            }
        }
        return false;
    }

    /**
     * The boundaries above that no longer exist, which is none.
     *
     * <p>A name that has been renamed or removed is a boundary this stops at and nothing keeps: the
     * walk would run straight through the place that was holding the promise, and what it then
     * found would be about whatever is there now. So the names are held against what was compiled
     * rather than being a list somebody remembers to keep.
     */
    Set<String> boundariesThatAreNotThere() {
        Set<String> gone = new HashSet<>(WHERE_A_WALK_STOPS);
        gone.removeAll(byName.keySet());
        return gone;
    }

    /** Whether this method calls {@code owner#member}. */
    private static boolean asks(MethodModel method, String owner, String member) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(owner)
                        && call.name().stringValue().equals(member));
    }

    /** Whether any parameter of this method is somewhere a walk of something can be put. */
    private static boolean hasSomewhereToPutAWalk(MethodModel method) {
        for (var parameter : method.methodTypeSymbol().parameterList()) {
            String named = parameter.isClassOrInterface()
                    ? parameter.descriptorString() : "";
            if (named.startsWith("L") && named.endsWith(";")
                    && A_WALK_ARRIVES_IN.contains(named.substring(1, named.length() - 1))) {
                return true;
            }
        }
        return false;
    }

    /** What this method calls, by name — the calls it writes and the ones a method reference makes.
     *  Reached by name and not by descriptor, so an overload of a name this finds is one it says is
     *  called, which is the wider answer and the one a guard wants. */
    private static List<String> calledBy(MethodModel method) {
        List<String> out = new ArrayList<>();
        method.code().stream().flatMap(code -> code.elementStream()).forEach(element -> {
            if (element instanceof InvokeInstruction call) {
                out.add(call.owner().asInternalName() + "#" + call.name().stringValue());
            } else if (element instanceof InvokeDynamicInstruction made) {
                for (var argument : made.bootstrapArgs()) {
                    if (argument instanceof DirectMethodHandleDesc handle) {
                        String owner = handle.owner().descriptorString();
                        out.add(owner.substring(1, owner.length() - 1) + "#"
                                + handle.methodName());
                    }
                }
            }
        });
        return out;
    }
}
