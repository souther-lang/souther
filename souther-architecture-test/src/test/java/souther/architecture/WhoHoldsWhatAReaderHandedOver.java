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
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

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
 * <p><b>A method is what it is called and what it takes.</b> Two methods of one name are two
 * methods, and one of them taking a walk says nothing about the other; keyed by the name alone, a
 * helper taking a collection and a helper of that name taking a number are one entry, and whichever
 * of them was read last is the one a rule then asks about. That is the wrong way round from what a
 * guard wants, and it is silent — so the key is the name and what the method takes, both here and
 * at every call site.
 *
 * <p><b>A call reaches what may answer it.</b> Which method a call arrives at is settled at run
 * time where the name is declared by something with implementations, so a call is followed to every
 * method compiled here that could answer it: the one the call names, and the same name and
 * parameters under anything that stands in for it. Wider than what one run takes, which is the
 * direction a guard is worth having in — the other way round, a walk handed to an implementation
 * through the name of what it implements would be a walk this never followed.
 *
 * <p>Method references are calls. A walk handed to {@code this::something} arrives there as surely
 * as one handed over by name, and the name is in the handle the call site was built with.
 *
 * <p><b>What this does not follow, said rather than left to be found.</b> A walk handed through a
 * parameter that is not a collection does not arrive anywhere this looks — which is what a walk
 * given to something taking {@code Object} is, and what every functional interface's own method
 * takes once its type has been erased. A method reference is still followed, because the handle
 * names the method it stands for and that method takes what it takes; an instance of such an
 * interface held in a field and called later is not. Widening to {@code Object} would make every
 * method that takes anything at all a place a walk may be, which is not a reading of anything. So
 * this is a limit of what these rules say, and a reader that hands a walk through one of those is
 * one the census behind issue #1760 sees and this does not.
 *
 * <p><b>And it stops where the order does.</b> A walk handed to something that sorts it, or that
 * answers with the one element a collection was proved to hold, does not arrive on the other side in
 * the order it left in — so what happens there is about the order that place decided and not about
 * the one the value never had. Those places are named below, few, and each of them says at its own
 * boundary what it promises.
 */
final class WhoHoldsWhatAReaderHandedOver {

    /**
     * Where a walk stops being the walk it arrived as.
     *
     * <p>Each of these answers in an order it decided: the one element a collection holds, the
     * order a name gives, the order an atom domain gives. Whether each of them keeps that promise is
     * its own to say and is said where it is written — {@code TheOnly} refuses a collection that is
     * not of one, {@code PlanOrder} refuses a key that fails to tell two unequal items apart, and
     * {@code CanonicalOrder#walking} refuses two positions an order cannot tell apart. This is a
     * list of promises and not of exemptions, which is why it is checked against what exists
     * ({@link #boundariesThatAreNotThere}).
     *
     * <p>By the name and not by what each takes, which is the one place that is right: every method
     * of these names answers in an order it decided, so a walk handed to any of them stops. A name
     * put here whose methods do not all do that is a hole, which is why there are few of them and
     * each is a place that says what it promises.
     */
    static final Set<String> WHERE_A_WALK_STOPS = Set.of(
            "souther/compiler/values/TheOnly#of",
            "souther/compiler/values/InOneOrder#of",
            "souther/compiler/values/PlanOrder#inOrder",
            "souther/compiler/values/PlanOrder#canonical",
            "souther/compiler/numeric/CanonicalOrder#walking",
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
     *
     * <p>Said as the few things a walk is, and asked of a type by whether it is one of them rather
     * than by whether it is spelled as one ({@link #isAKindOf}). A parameter written as the
     * collection it will be handed is as much somewhere a walk arrives as one written as the
     * interface, and a rule that read the spelling would follow the second and not the first.
     */
    private static final Set<String> A_WALK_ARRIVES_IN = Set.of(
            "java/util/Collection", "java/util/Map", "java/lang/Iterable",
            "java/util/Iterator", "java/util/stream/BaseStream");

    /** Each method by what it is called and what it takes, which is what tells two of one name
     *  apart. */
    private final Map<String, MethodModel> byWhatItIs = new HashMap<>();

    /** What each of them calls, as the methods compiled here that could answer each call. */
    private final Map<String, Set<String>> calls = new HashMap<>();

    private final Set<String> canBeHandedAWalk = new HashSet<>();

    /** Every class here, under each name it may be reached by — itself and whatever it stands in
     *  for. */
    private final Map<String, Set<String>> standingInFor = new HashMap<>();

    /** Each class here against every name it is: itself, what it extends, what it implements. The
     *  other way round from {@link #standingInFor}, and what says whether a type is a kind of
     *  something. */
    private final Map<String, Set<String>> knownAs = new HashMap<>();

    /** What each name is as a loaded class, or empty where nothing here can load it. Remembered
     *  because the question is asked of the same few names at every method. */
    private final Map<String, Optional<Class<?>>> asLoaded = new HashMap<>();

    /**
     * The reading of each population, kept for as long as the fork that built it.
     *
     * <p>Building one is a walk over every class this repository compiled and over every call each
     * of their methods makes, and none of what it reads moves while the tests run — the compile
     * that produced it happened before any of them started. A rule here asks the same population
     * the same question once per check it has, and each of those checks was paying for the walk
     * again.
     */
    private static final Map<CompiledOutputs, WhoHoldsWhatAReaderHandedOver> BUILT =
            new ConcurrentHashMap<>();

    /** What was handed over in {@code where}, read once however many rules ask. */
    static WhoHoldsWhatAReaderHandedOver of(CompiledOutputs where) {
        return BUILT.computeIfAbsent(where, WhoHoldsWhatAReaderHandedOver::new);
    }

    /** Every method compiled in {@code where}, with what each of them calls. */
    private WhoHoldsWhatAReaderHandedOver(CompiledOutputs where) {
        List<ClassModel> read = where.all();
        for (ClassModel each : read) {
            String owner = each.thisClass().name().stringValue();
            Set<String> named = everythingItIs(each, read);
            knownAs.put(owner, named);
            for (String one : named) {
                standingInFor.computeIfAbsent(one, _ -> new HashSet<>()).add(owner);
            }
        }
        // Every method first and what each of them calls afterwards. A call is followed to the
        // methods compiled here that could answer it, so answering one before they have all been
        // read is answering it against however much of this had been built — which is an edge that
        // depends on the order the classes were walked in, in a reading about exactly that.
        for (ClassModel each : read) {
            String owner = each.thisClass().name().stringValue();
            for (MethodModel method : each.methods()) {
                String what = owner + "#" + method.methodName().stringValue()
                        + method.methodType().stringValue();
                byWhatItIs.put(what, method);
                if (hasSomewhereToPutAWalk(method)) {
                    canBeHandedAWalk.add(what);
                }
            }
        }
        byWhatItIs.forEach((what, method) -> calls.put(what, whatItCalls(method)));
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
        byWhatItIs.forEach((what, method) -> {
            if (asks(method, owner, member)) {
                holding.add(what);
                toFollow.add(what);
            }
        });
        while (!toFollow.isEmpty()) {
            for (String called : calls.getOrDefault(toFollow.remove(), Set.of())) {
                if (canBeHandedAWalk.contains(called) && !stopsAt(called)
                        && holding.add(called)) {
                    toFollow.add(called);
                }
            }
        }
        return holding;
    }

    /** The method this is of, for a rule that reads what it does. */
    MethodModel methodThatIs(String what) {
        return byWhatItIs.get(what);
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
        Set<String> named = new HashSet<>();
        byWhatItIs.keySet().forEach(what -> named.add(what.substring(0, what.indexOf('('))));
        Set<String> gone = new HashSet<>(WHERE_A_WALK_STOPS);
        gone.removeAll(named);
        return gone;
    }

    /** Whether a walk handed here stops, which is asked of the name since every method of these
     *  names answers in an order it decided. */
    private static boolean stopsAt(String what) {
        return WHERE_A_WALK_STOPS.contains(what.substring(0, what.indexOf('(')));
    }

    /** Whether this method calls {@code owner#member}. */
    private static boolean asks(MethodModel method, String owner, String member) {
        return method.code().stream().flatMap(code -> code.elementStream())
                .anyMatch(element -> element instanceof InvokeInstruction call
                        && call.owner().asInternalName().equals(owner)
                        && call.name().stringValue().equals(member));
    }

    /** Whether any parameter of this method is somewhere a walk of something can be put. */
    private boolean hasSomewhereToPutAWalk(MethodModel method) {
        for (var parameter : method.methodTypeSymbol().parameterList()) {
            if (isOneOf(parameter.descriptorString(), A_WALK_ARRIVES_IN)) {
                return true;
            }
        }
        return false;
    }

    /** Whether the type this descriptor names is a kind of any of {@code these}. */
    private boolean isOneOf(String descriptor, Set<String> these) {
        if (!descriptor.startsWith("L") || !descriptor.endsWith(";")) {
            return false;
        }
        String named = descriptor.substring(1, descriptor.length() - 1);
        return these.stream().anyMatch(one -> isAKindOf(named, one));
    }

    /**
     * Whether {@code type} is a kind of {@code wanted}.
     *
     * <p><b>Asked of what a type is and not of what it is called.</b> A method handing back an
     * {@code ArrayList} hands back a list; one handing back a class written here that implements a
     * list does too. A rule written over the names of the interfaces would follow the method that
     * says {@code List} and pass over the one that says what kind of list — which is the same hole
     * as naming the ways a list gets built, one level up.
     *
     * <p>Answered from what was compiled here first, because that is the hierarchy this already
     * holds, and from the class itself where it can be loaded — which is how a type of the
     * platform's, named by nothing compiled here, is reached.
     */
    private boolean isAKindOf(String type, String wanted) {
        if (type.equals(wanted)) {
            return true;
        }
        Set<String> named = knownAs.get(type);
        if (named != null && named.contains(wanted)) {
            return true;
        }
        Optional<Class<?>> one = asLoaded(type);
        Optional<Class<?>> other = asLoaded(wanted);
        return one.isPresent() && other.isPresent() && other.get().isAssignableFrom(one.get());
    }

    /** The class this name is, where anything here can load it. */
    private Optional<Class<?>> asLoaded(String type) {
        return asLoaded.computeIfAbsent(type, named -> {
            try {
                return Optional.of(Class.forName(named.replace('/', '.'), false,
                        WhoHoldsWhatAReaderHandedOver.class.getClassLoader()));
            } catch (ClassNotFoundException | LinkageError unreachable) {
                // Compiled somewhere this test does not have on its path. What such a type is, is
                // whatever the hierarchy above said it was.
                return Optional.empty();
            }
        });
    }

    /** What this method calls: every method compiled here that could answer each of its call
     *  sites, and the one each method reference names. */
    private Set<String> whatItCalls(MethodModel method) {
        Set<String> out = new HashSet<>();
        method.code().stream().flatMap(code -> code.elementStream()).forEach(element -> {
            if (element instanceof InvokeInstruction call) {
                out.addAll(whatMayAnswer(call.owner().asInternalName(),
                        call.name().stringValue() + call.type().stringValue()));
            } else if (element instanceof InvokeDynamicInstruction made) {
                for (var argument : made.bootstrapArgs()) {
                    if (argument instanceof DirectMethodHandleDesc handle) {
                        String owner = handle.owner().descriptorString();
                        out.addAll(whatMayAnswer(owner.substring(1, owner.length() - 1),
                                handle.methodName() + handle.lookupDescriptor()));
                    }
                }
            }
        });
        return out;
    }

    /** Every method compiled here that a call naming {@code owner} and {@code signature} may
     *  arrive at — the one it names, and the same signature under anything standing in for it. */
    private Set<String> whatMayAnswer(String owner, String signature) {
        Set<String> out = new HashSet<>();
        for (String standing : standingInFor.getOrDefault(owner, Set.of())) {
            String what = standing + "#" + signature;
            if (byWhatItIs.containsKey(what)) {
                out.add(what);
            }
        }
        return out;
    }

    /** Every name this class may be reached by: itself, what it extends and what it implements, as
     *  far as any of those are compiled here. */
    private static Set<String> everythingItIs(ClassModel of, List<ClassModel> here) {
        Map<String, ClassModel> byName = new HashMap<>();
        here.forEach(each -> byName.put(each.thisClass().name().stringValue(), each));
        Set<String> out = new HashSet<>();
        Deque<ClassModel> toRead = new ArrayDeque<>(List.of(of));
        while (!toRead.isEmpty()) {
            ClassModel each = toRead.remove();
            if (!out.add(each.thisClass().name().stringValue())) {
                continue;
            }
            List<String> above = new ArrayList<>();
            each.superclass().ifPresent(one -> above.add(one.asInternalName()));
            each.interfaces().forEach(one -> above.add(one.asInternalName()));
            above.forEach(one -> {
                ClassModel found = byName.get(one);
                if (found != null) {
                    toRead.add(found);
                }
            });
        }
        return out;
    }

    /**
     * What takes something out of a walk by where it is rather than by what it is.
     *
     * <p>Named by what is called and not by where the call goes, since a method that does one of
     * these while holding a walk has the order in its answer whatever it does next.
     */
    private static final Set<String> BY_WHERE_IT_IS = Set.of(
            "getFirst", "getLast", "findFirst", "indexOf", "lastIndexOf",
            "limit", "skip", "reduce", "toArray", "listIterator",
            "firstKey", "lastKey", "firstEntry", "lastEntry", "first", "last");

    /**
     * And what keeps the walk it took, which is the same order read a different way.
     *
     * <p>A walk of a value that holds no order, gathered into something whose equality sees one, is
     * the whole of what this is about: two writings of one value are one value, and the sequences
     * they come to are two. So a reader that hands one back, joins one into a text, or walks one in
     * the order it came is one of these as surely as a reader that takes the first of them.
     */
    private static final Set<String> KEEPS_THE_ORDER_IT_WALKED = Set.of(
            "java/util/List#copyOf",
            "java/util/stream/Stream#toList",
            "java/util/stream/Stream#toArray",
            "java/util/stream/Stream#forEachOrdered",
            "java/util/stream/Collectors#toList",
            "java/util/stream/Collectors#toUnmodifiableList",
            "java/util/stream/Collectors#joining",
            "java/util/Collection#toArray",
            "java/lang/String#join");

    /**
     * What a method hands back that has an order in it.
     *
     * <p><b>Asked of the type and not of how it was built, because the spelling is endless.</b> A
     * walk poured into a list has the order in the answer whether the list was made by
     * {@code List.copyOf}, by {@code toList}, by {@code new ArrayList<>(…)}, by
     * {@code new LinkedList<>(…)} or by something nobody here has thought of — what makes it the
     * defect is that the thing handed back is equal to another only where the two are in one order.
     * Named by what is called, this would be a list somebody has to keep adding to, and the day it
     * is one short it says a reader is fine.
     *
     * <p>So a method holding a walk whose answer is one of these is read. Some of them turn out to
     * be walks of something else, or walks whose order came from somewhere that decided it — that
     * is a fact about the body, and it is written down where the rule is rather than guessed at
     * here.
     *
     * <p>A set is not one of these, however it is held. A {@code LinkedHashSet} keeps the order it
     * was filled in and is equal to any set of the same things, so handing one back does not put
     * the order in the answer — what a reader of it then does is that reader's to answer for.
     */
    private static final Set<String> AN_ANSWER_WITH_AN_ORDER_IN_IT = Set.of(
            "java/util/Collection", "java/util/Iterator", "java/util/stream/BaseStream",
            "java/lang/CharSequence", "java/util/StringJoiner");

    /**
     * Whether what this method hands back may have an order in it — a walk of anything, a text, or
     * an array of either.
     *
     * <p><b>Every collection and not the sequences alone.</b> What a method says it hands back is
     * not what it hands back: a method written to give a {@code Collection} gives whatever it
     * built, and a list built inside it is a list to everyone who receives it. So a walk handed
     * back at all is read, and the ones that really are sets — two of which are one whatever order
     * either was filled in — say so where the rule is written rather than being passed over here on
     * the strength of a declared type.
     */
    private boolean theAnswerMayHaveAnOrderInIt(MethodModel method) {
        String gives = method.methodTypeSymbol().returnType().descriptorString();
        return gives.startsWith("[") || isOneOf(gives, AN_ANSWER_WITH_AN_ORDER_IN_IT);
    }

    /**
     * Whether this method reads a walk for where things are in it.
     *
     * <p>Asked of what the method calls and of what it hands back, and not of what the walk it
     * holds reaches. A method with one of these in it either does it to what it was handed, which
     * is the defect, or does it to something else while holding a walk, which is a method doing two
     * things and is worth being told about either way.
     */
    boolean readsAWalkForWhereThingsAre(MethodModel method) {
        if (theAnswerMayHaveAnOrderInIt(method)) {
            return true;
        }
        return takesSomethingByWhereItIs(method);
    }

    /** The reads that are one whatever the method goes on to hand back. */
    private boolean takesSomethingByWhereItIs(MethodModel method) {
        List<InvokeInstruction> made = method.code().stream()
                .flatMap(code -> code.elementStream())
                .filter(InvokeInstruction.class::isInstance)
                .map(InvokeInstruction.class::cast)
                .toList();
        return made.stream().anyMatch(call -> BY_WHERE_IT_IS.contains(call.name().stringValue())
                        || KEEPS_THE_ORDER_IT_WALKED.contains(call.owner().asInternalName()
                                + "#" + call.name().stringValue())
                        || isReadingAListByIndex(call)
                        || isGatheringIntoASequence(call))
                || asksAWalkForItsFirstAndNothingElse(made);
    }

    /**
     * A walk poured into something whose own equality sees what order it was poured in.
     *
     * <p>Which is what tells this from a walk poured into a set. A {@code LinkedHashSet} keeps the
     * order it was filled in and is equal to any set of the same things, so filling one is not yet
     * an answer that has the order in it; a list of the same things is two lists where the walk went
     * two ways, and so is a text built a piece at a time.
     */
    private boolean isGatheringIntoASequence(InvokeInstruction call) {
        String owner = call.owner().asInternalName();
        return (isAKindOf(owner, "java/util/List") && call.name().stringValue().equals("<init>"))
                || (isAKindOf(owner, "java/lang/Appendable")
                        && call.name().stringValue().equals("append"));
    }

    /** {@code get} of a list or of an iterator's place, which a map is asked the same word. Asked
     *  of what the thing is rather than of what it is spelled as, for the reason above. */
    private boolean isReadingAListByIndex(InvokeInstruction call) {
        return call.name().stringValue().equals("get")
                && isAKindOf(call.owner().asInternalName(), "java/util/List");
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
}
