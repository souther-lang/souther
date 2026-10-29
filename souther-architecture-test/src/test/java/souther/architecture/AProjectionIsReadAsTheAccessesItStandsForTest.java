package souther.architecture;

import org.junit.jupiter.api.Test;

import java.lang.classfile.ClassModel;
import java.lang.classfile.MethodModel;
import java.lang.classfile.instruction.InvokeDynamicInstruction;
import java.lang.classfile.instruction.InvokeInstruction;
import java.lang.classfile.instruction.TypeCheckInstruction;
import java.lang.constant.ClassDesc;
import java.lang.constant.ConstantDesc;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A walk over a tree reads a {@code FieldProjection} as the field accesses it stands for, or says
 * why the difference does not reach it.
 *
 * <p>A projection holds a run of names read off one value as one node, so that how many there are
 * is not how deep the tree is. Written out as accesses, the run was a node per name, and those
 * nodes were two things at once: the slots a walk goes down, and the subexpressions a walk asks
 * about. A projection keeps the first — its base is its one child — and not the second: the
 * projections shorter than it are subexpressions of it that no walk meets by going down. So every
 * walk is one of six, and this is where each says which.
 *
 * <ul>
 *   <li>It asks about the tree's structure — what is evaluated, what a binding reads, which slots
 *       there are, where a choice or a call stands — and no name read adds anything to that, so the
 *       base is all there is to go down to.</li>
 *   <li>It asks each node it meets what it is — a position, a subject, a term — and wants the answer
 *       for every subexpression standing there ({@code Core.subexpressionsAt}), which is the node
 *       and the projections shorter than it, in the order the descent met them.</li>
 *   <li>It asks which of the subexpressions standing there a table of subjects holds first, and
 *       stops there ({@code Terms.heldAt}). One answer and not every one, so it goes down the names
 *       once against the table: naming each shorter projection to look it up costs the square of
 *       the projection, and a projection the table stops short of is named all the way down.</li>
 *   <li>It is the rule for a field access itself, and reads it along a projection's names.</li>
 *   <li>It is handed one access and asks of it and its target alone.</li>
 *   <li>It reads only a tree that runs, which holds no projection.</li>
 * </ul>
 *
 * <p>The population is every method that goes down a tree through the walks the language keeps
 * ({@code Core.forEachChild}, {@code ScopeStep.forEachChild}, {@code Core.mapAll},
 * {@code Core.mapChildren}) or by hand through a field access's target. A method the table does not
 * name is red, and so is a row naming a method that no longer is one. A row of the second kind is
 * red where the method does not ask through {@code Core.subexpressionsAt}; one of the third where it
 * does not ask through {@code Terms.heldAt}, or names every subexpression besides; one of the fourth
 * where it never reads a projection.
 *
 * <p>Asking through the one method is what is held, rather than each walk's own loop over a
 * projection's names. Which subexpressions stand at a node is a single answer
 * ({@code AValueAGuaranteeWalkReachesIsOneNodeHoweverFarDownTest} holds it to the accesses written
 * out), and a walk that wrote its own would be a second one nothing compares. Which of them a table
 * holds first is that answer looked up, and {@code ATableIsAskedOfAProjectionAsOfEachShorterOneTest}
 * holds {@code Terms.heldAt} to it.
 */
class AProjectionIsReadAsTheAccessesItStandsForTest {

    private static final String CORE = "souther/compiler/core/Core";

    private static final String PROJECTION = CORE + "$FieldProjection";

    private static final String SCOPE_STEP = "souther/compiler/check/ScopeStep";

    /** What a walk asking each node names where it asks every subexpression standing there. */
    private static final String SUBEXPRESSIONS_AT = CORE + "#subexpressionsAt";

    private static final String TERMS = "souther/compiler/check/Terms";

    /** What a walk asking which subexpression a table holds names where it asks that. */
    private static final String HELD_AT = TERMS + "#heldAt";

    private static final CompiledOutputs PUBLISHED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    /** How a walk reads a projection. */
    private enum Reading {

        /** Its question is about the tree's structure, and the base is the one child. */
        STRUCTURE,

        /** It asks each node what it is, and wants it of every subexpression standing there. */
        EACH_SUBEXPRESSION,

        /** It asks which subexpression standing there a table holds first, and stops there. */
        FIRST_HELD,

        /** It is the rule for a field access, read along a projection's names. */
        NAMES,

        /** It is handed one access and asks of it and its target, and of nothing under them; a
         *  projection reaches it as its last access, read off the projection one name shorter. */
        ONE_ACCESS,

        /** It reads only a tree that runs, which holds no projection. */
        THE_TREE_THAT_RUNS
    }

    private record Row(Reading reading, String why) {}

    private static final Map<String, Row> WALKS = walks();

    /** Every walk the compiled classes hold, read once for the three questions below. */
    private static final Map<String, Set<String>> FOUND = walkers(PUBLISHED.all());

    @Test
    void everyWalkOverATreeSaysHowItReadsAProjection() {
        assertFalse(FOUND.isEmpty(), "no walk over a tree was found, so the rule is asked of nothing");
        assertEquals(new TreeSet<>(WALKS.keySet()), new TreeSet<>(FOUND.keySet()),
                "a method going down a Core tree that does not say how it reads a FieldProjection."
                        + " Say which it is in WALKS: a question about structure, a question asked"
                        + " of every subexpression, the first subexpression a table holds, the rule"
                        + " for a field access, a question about one access, or a reader of the"
                        + " tree that runs");
    }

    @Test
    void aWalkThatAsksEachNodeAsksEverySubexpressionStandingThere() {
        Set<String> unasked = new TreeSet<>();
        WALKS.forEach((method, row) -> {
            if (row.reading() == Reading.EACH_SUBEXPRESSION
                    && !FOUND.getOrDefault(method, Set.of()).contains(SUBEXPRESSIONS_AT)) {
                unasked.add(method);
            }
        });
        assertEquals(Set.of(), unasked,
                "a walk that asks each node what it is, and does not ask it of every subexpression"
                        + " standing there through Core.subexpressionsAt");
    }

    @Test
    void aWalkThatLooksForTheFirstHeldAsksTheTableAlongTheNames() {
        Set<String> unasked = new TreeSet<>();
        WALKS.forEach((method, row) -> {
            Set<String> named = FOUND.getOrDefault(method, Set.of());
            if (row.reading() == Reading.FIRST_HELD
                    && (!named.contains(HELD_AT) || named.contains(SUBEXPRESSIONS_AT))) {
                unasked.add(method);
            }
        });
        assertEquals(Set.of(), unasked,
                "a walk that looks for the first subexpression a table holds, and does not ask"
                        + " Terms.heldAt, or names every subexpression besides: each shorter"
                        + " projection named to look it up is a term as long as itself");
    }

    @Test
    void theRuleForAFieldAccessReadsAProjectionToo() {
        Set<String> unread = new TreeSet<>();
        WALKS.forEach((method, row) -> {
            if (row.reading() == Reading.NAMES
                    && !FOUND.getOrDefault(method, Set.of()).contains(PROJECTION)) {
                unread.add(method);
            }
        });
        assertEquals(Set.of(), unread,
                "the rule for a field access, written where nothing reads a projection's names");
    }

    /**
     * Every method going down a tree, with what it names in its code — the classes it calls, tests
     * a value for and has a switch case for, and {@code Core.subexpressionsAt} where it asks it —
     * its lambdas' counted as its own.
     */
    private static Map<String, Set<String>> walkers(Iterable<ClassModel> classes) {
        Map<String, Set<String>> calls = new TreeMap<>();
        Set<String> walking = new TreeSet<>();
        for (ClassModel owner : classes) {
            String self = owner.thisClass().asInternalName();
            if (self.equals(CORE) || self.startsWith(CORE + "$")) {
                continue;
            }
            WhereALambdaIsWritten lambdas = WhereALambdaIsWritten.in(owner);
            for (MethodModel method : owner.methods()) {
                if (method.code().isEmpty()) {
                    continue;
                }
                String at = lambdas.enclosing(AMethod.of(owner, method));
                if (at.equals(AMethod.of(SCOPE_STEP, "forEachChild",
                        "(L" + CORE + ";Ljava/util/function/BiConsumer;)V"))) {
                    continue;
                }
                Set<String> mentioned = calls.computeIfAbsent(at, _ -> new TreeSet<>());
                for (var element : method.code().orElseThrow()) {
                    switch (element) {
                        case InvokeInstruction call -> {
                            mentioned.add(call.owner().asInternalName());
                            if (call.owner().asInternalName().equals(CORE)
                                    && call.name().equalsString("subexpressionsAt")) {
                                mentioned.add(SUBEXPRESSIONS_AT);
                            }
                            if (call.owner().asInternalName().equals(TERMS)
                                    && call.name().equalsString("heldAt")) {
                                mentioned.add(HELD_AT);
                            }
                            if (goesDown(call.owner().asInternalName(),
                                    call.name().stringValue())) {
                                walking.add(at);
                            }
                        }
                        case TypeCheckInstruction check ->
                                mentioned.add(check.type().asInternalName());
                        case InvokeDynamicInstruction indy -> {
                            for (ConstantDesc each : indy.bootstrapArgs()) {
                                if (each instanceof ClassDesc type && type.isClassOrInterface()) {
                                    String descriptor = type.descriptorString();
                                    mentioned.add(descriptor.substring(1, descriptor.length() - 1));
                                }
                            }
                        }
                        default -> { }
                    }
                }
            }
        }
        Map<String, Set<String>> out = new LinkedHashMap<>();
        walking.forEach(each -> out.put(each, calls.get(each)));
        return out;
    }

    /** Whether calling {@code name} of {@code owner} is going down a tree. */
    private static boolean goesDown(String owner, String name) {
        return (owner.equals(CORE) && Set.of("forEachChild", "mapAll", "mapChildren").contains(name))
                || (owner.equals(SCOPE_STEP) && name.equals("forEachChild"))
                || (owner.equals(CORE + "$FieldAccess") && name.equals("target"));
    }

    /** What evaluating a node runs, which reading a name adds nothing to. */
    private static final String EVALUATION = "what a node evaluates or ends a run with: reading a"
            + " name runs nothing and ends nothing, so what a projection evaluates is its base";

    /** Which bindings are read, which no name read is. */
    private static final String BINDINGS = "which bindings a tree reads or binds: a name read off a"
            + " value is no binding, so a projection reads what its base reads";

    /** Looks for the first subexpression a table holds. */
    private static final String FINDS_THE_FIRST_HELD = "asks which subexpression standing at each"
            + " node a table of this value's subjects holds, and stops at the first: a position names"
            + " itself and nothing under it is one of its own";

    /** A choice, a binding or a call found in a tree, which no name read is. */
    private static final String CHOICES_AND_CALLS = "looks for a choice, a binding, a call or a"
            + " comparison: a name read off a value is none of them, so nothing between a"
            + " projection and its base is one";

    /** A rewrite whose targets are never a name read. */
    private static final String REWRITES_THE_BASE = "a rewrite whose targets are a binding's reads"
            + " or a choice, which no name read off a value is: the base is the one slot, and"
            + " rewriting it leaves the names read off it";

    /** Asks each node, and asks the shorter projections too. */
    private static final String ASKS_EACH = "asks each node it meets what it is, and asks it of"
            + " every subexpression standing there, as the descent would have met them";

    /** Reads the names off the projection, a name at a time. */
    private static final String READS_THE_NAMES = "the rule for a field access, read along the"
            + " projection's names rather than down the stack";

    /** One access and its target. */
    private static final String ONE = "handed one access, and asks whether its target is a place"
            + " through the reading of places, which reads a projection's names itself";

    /** The tree that runs. */
    private static final String RUNS = "reads the tree that runs or is emitted, which reads a field"
            + " an access at a time and holds no projection";

    private static Map<String, Row> walks() {
        Map<String, Row> out = new LinkedHashMap<>();
        String c = "souther/compiler/";
        String core = "L" + CORE + ";";
        String at = "L" + c + "check/Denotations;";
        String reads = "L" + c + "inputs/InputReads;";
        row(out, c + "abort/AbortSites", "walk", "(" + core + "L" + c
                + "core/KernelContracts;Ljava/util/Map;Ljava/util/IdentityHashMap;)V",
                Reading.STRUCTURE, EVALUATION);
        row(out, c + "abort/AbortSites", "walkGuarded", "(L" + CORE + "$Construct;L" + c
                + "core/KernelContracts;Ljava/util/Map;Ljava/util/IdentityHashMap;)V",
                Reading.STRUCTURE, EVALUATION);
        row(out, c + "check/AdmissibleReading", "gather",
                "(" + core + "Ljava/util/Set;" + at + "Ljava/util/Set;)V",
                Reading.FIRST_HELD, FINDS_THE_FIRST_HELD);
        row(out, c + "check/AffineForms", "composed", "(" + core + "Ljava/lang/Object;L" + c
                + "check/AffineForms$Reading;L" + c + "check/AffineForms$Walk;L" + c
                + "check/AffineForms$Stop;)L" + c + "numeric/LinearForm;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/AffineForms", "isANewtypesValue", "(L" + CORE + "$FieldAccess;L" + c
                + "check/AffineForms$Reading;)Z", Reading.ONE_ACCESS,
                "asks of one access the type of its target, which says whether the field is the"
                        + " value a newtype wraps; a projection reaches it as its last access, whose"
                        + " target is the projection one name shorter and has a type of its own");
        row(out, c + "check/ValueStanding", "eliminated", "(" + core + "Ljava/lang/Object;L" + c
                + "check/ValueStanding$Names;L" + c + "check/BindingWalk;)Ljava/util/List;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/ValueStanding", "theConstructionAndItsRestEndNone",
                "(L" + c + "core/Core$FieldAccess;Ljava/lang/Object;L" + c
                        + "check/ValueStanding$Names;L" + c
                        + "check/BindingWalk;Ljava/util/function/Predicate;)Z",
                Reading.ONE_ACCESS,
                "asks of one access the construction it is read off and the parts of it other"
                        + " than the field it reads");
        row(out, c + "check/ElementsApart", "readOff", "(" + core + "L" + c
                + "check/DeclarationNewtypes;)L" + c + "check/ElementsApart$ReadOff;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/ElementsApart", "bindingUnder",
                "(" + core + ")L" + c + "types/BindingId;", Reading.STRUCTURE,
                "asks which binding a run of fields is read off, which is the base");
        row(out, c + "check/EntryHeld", "isTheValue",
                "(" + core + "L" + c + "types/BindingId;)Z", Reading.STRUCTURE,
                "asks whether a value is a binding or the value a name wraps read off one, which"
                        + " the base answers");
        row(out, c + "check/SidesBalanced", "stepsFrom",
                "(" + core + "L" + c + "types/BindingId;)Ljava/util/List;", Reading.STRUCTURE,
                "reads the run of fields taken off one binding, which the base answers");
        row(out, c + "partition/WhatARunWorksOutBeforeACount", "offTheParameter",
                "(" + core + "L" + c + "types/BindingId;)Z", Reading.STRUCTURE,
                "asks whether a value is a parameter or a run of fields read off one, which the"
                        + " base answers");
        row(out, c + "partition/WhatARunWorksOutBeforeACount", "wayDownTo",
                "(" + core + core + ")Ljava/util/List;", Reading.STRUCTURE,
                "finds the way down to one node by identity, which a projection's base is on");
        row(out, c + "partition/WhatARunWorksOutBeforeACount$Within", "letsThrough",
                "(" + core + ")Z", Reading.EACH_SUBEXPRESSION, ASKS_EACH);
        row(out, c + "check/FieldDomains", "readOffAsItStands", "(" + core + ")Z",
                Reading.STRUCTURE, "asks whether a value is a name or a run of fields read off"
                        + " one, which the base answers");
        row(out, c + "partition/AffineReading", "isAPlainRead", "(" + core + ")Z",
                Reading.STRUCTURE, "asks whether a value is a name or a run of fields read off"
                        + " one, with nothing between it and the place, which the base answers");
        row(out, c + "check/AnalysisBody", "visit", "(" + core + "L" + c
                + "check/ValueTemplates;Ljava/util/Set;Ljava/util/List;)V",
                Reading.STRUCTURE, "finds the builds of values, which no name read is");
        row(out, c + "check/ADeclarationsWitness$Pools", "mention", "(" + core
                + "Ljava/util/List;Ljava/util/List;Ljava/util/List;)V", Reading.STRUCTURE,
                "collects the numbers and the text a rule writes, which stand at its leaves"
                        + " and not among the names read off a value");
        row(out, c + "check/RecursionOverAList", "callsOf", "(" + core + "L" + c
                + "types/ValueName$Helper;Ljava/util/List;)V", Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/Clauses$ReadsOfAClause", "walk", "(" + core + ")V",
                Reading.STRUCTURE, "a chain read off one of the value's fields is one place, whose"
                        + " names Location.of reads; a projection read off anything else names"
                        + " no place, so its base is all there is to go down to");
        row(out, c + "inputs/InputReads", "walkNames", "(" + core + "Ljava/util/Set;Ljava/util/Set;)V",
                Reading.STRUCTURE, BINDINGS);
        row(out, c + "flow/ValueArrivals", "readCopies", "(" + core + "L" + c
                + "types/OccurrenceLineage$Expansion;)V", Reading.STRUCTURE,
                "which copy of an application each node is code of: a name read off a value says"
                        + " nothing of where it is written, so a projection is where its base is");
        row(out, c + "inputs/InputReads", "applicationsRead",
                "(" + core + "Ljava/util/Set;Ljava/util/Set;)V", Reading.STRUCTURE, BINDINGS);
        row(out, c + "check/Clauses", "substituted", "(" + core + "Ljava/util/Map;)" + core,
                Reading.STRUCTURE, REWRITES_THE_BASE);
        row(out, c + "check/ElementBindings", "walk", "(" + core + "Ljava/util/Map;Ljava/util/Map;L"
                + c + "check/ElementProvenance;Ljava/util/Map;Ljava/util/Map;)V",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/ClosureEntries", "visit", "(" + core + "L" + c
                + "check/ClosureEntries$Standing;)V", Reading.STRUCTURE,
                "finds the places a closure is used, which no field read is");
        row(out, c + "reading/KeptElements", "callWritten",
                "(" + core + "L" + c + "inputs/InputReads;L" + CORE + "$Call;)L" + c
                        + "reading/KeptElements$Written;", Reading.STRUCTURE,
                "finds the call of an operation that an expansion stands for, by the occurrence it"
                        + " applies, entering each scope on the way, which no field read is");
        row(out, c + "reading/ValueChoices", "forksInParts", "(" + core + "L" + c
                + "inputs/InputReads;L" + c + "check/ElementsWrittenOut$Reading;L" + c
                + "check/DeclarationNewtypes;I"
                + "Ljava/util/Set;Ljava/util/List;)V", Reading.STRUCTURE,
                "looks for a fork in a value and in what its names stand for, which no field read is:"
                        + " a projection is its base, and the base is a name followed the same way");
        row(out, c + "reading/ElementEvaluations", "writes", "(" + core + core + ")Z",
                Reading.STRUCTURE,
                "asks whether an expression is written anywhere in another, which no field read"
                        + " is: a projection is its base, and what is written in the base is"
                        + " written in it");
        row(out, c + "reading/KeptElements", "collect", "(" + core + "L" + CORE
                + "$Binary;Ljava/util/List;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "check/EmittedClassReferences", "visit", "(" + core + "L" + c + "types/Type;)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "check/EmittedClassReferences", "visitChildren",
                "(" + core + "L" + c + "types/Type;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "check/InvariantChecker", "bindingIn", "(" + core + ")L" + CORE + "$LetIn;",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/InvariantChecker", "collectAlike", "(" + core + "L" + c + "check/Term;"
                + at + "Ljava/util/Set;)V", Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/InvariantChecker", "relating", "(" + core + "L" + c
                + "types/TypeSymbol$AtModule;" + at + "L" + c
                + "check/InvariantChecker$Coordinates;Ljava/util/Map;)V",
                Reading.FIRST_HELD, FINDS_THE_FIRST_HELD);
        row(out, c + "check/InvariantChecker", "splitIn",
                "(" + core + ")L" + c + "check/InvariantChecker$SplitSite;",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/InvariantChecker", "walk", "(" + core + "L" + c + "check/Known;" + at
                + "L" + c + "check/ContextMultiplicity;)L" + c + "check/Known;",
                Reading.STRUCTURE, EVALUATION);
        row(out, c + "check/InvariantChecker", "without",
                "(" + core + "Ljava/util/Set;" + core + ")" + core,
                Reading.STRUCTURE, REWRITES_THE_BASE);
        row(out, c + "check/Location", "of", "(" + core + "L" + c
                + "check/DeclarationNewtypes;Ljava/util/function/Function;"
                + "Ljava/util/function/Function;)L" + c
                + "check/Location;", Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/PathReachability", "pathUnder",
                "(" + core + reads + ")L" + c + "inputs/TermPath;",
                Reading.NAMES, "a side read through a newtype's own value: of a"
                        + " projection, the projection one name shorter");
        row(out, c + "check/PathReachability", "unanswered", "(" + core + "L" + c
                + "coverage/CoverageSites$Plan;Ljava/util/Map;Ljava/util/Map;)Ljava/util/Optional;",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/PathReachability", "unreached",
                "(" + core + "L" + c + "check/PathReachability$Walked;" + at + reads + ")V",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/PathReachability", "appliedToNothing",
                "(" + core + "L" + c + "reach/Proof;)V", Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/Predicates", "names", "(" + core + "L" + c + "check/Term$Chains;" + at
                + ")Z",
                Reading.FIRST_HELD, FINDS_THE_FIRST_HELD);
        row(out, c + "check/Predicates$Reads", "chain", "(" + core + ")Ljava/util/List;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Extreme", "comparedAs",
                "(" + core + "Ljava/lang/Object;L" + c + "check/TheSignOfAnOrder$Sides;)L" + c
                        + "check/ValueStanding$ReadThrough;", Reading.NAMES,
                "asks whether the last name read is the value a newtype wears, which goes"
                        + " nowhere, and answers what it is read off");
        row(out, c + "check/StatedByClauses$Reading", "gather",
                "(" + core + "Ljava/util/Set;" + at + ")V", Reading.FIRST_HELD,
                FINDS_THE_FIRST_HELD);
        row(out, c + "check/TermMeaning", "project", "(" + core + "Ljava/util/List;)V",
                Reading.NAMES, "what a term says: a projection says what the accesses it"
                        + " stands for say, the last one first");
        row(out, c + "check/Terms", "chainInto", "(" + core + "Ljava/util/List;)V",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Terms", "keyOfNowhere", "(" + core + at + ")L" + c + "check/Term;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Terms", "namedByRule", "(" + core + at + ")Z",
                Reading.STRUCTURE, "asks whether every part is named by a rule, and a name read"
                        + " is a place exactly where its base is (Location.of): the projections"
                        + " between them answer what the base answers");
        row(out, c + "check/Terms", "rootBinding", "(" + core + ")L" + c + "types/BindingId;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Terms", "stepsAlong", "(" + core + ")L" + c + "check/Terms$Steps;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Terms", "subjectKey", "(" + core + at + ")L" + c + "check/Term;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "check/Terms$2", "readsThrough", "(L" + CORE + "$FieldAccess;" + at + ")Z",
                Reading.ONE_ACCESS, ONE);
        row(out, c + "check/ValueOrigin", "of", "(" + core + "Ljava/lang/Object;L" + c
                + "check/ValueOrigin$Reading;L" + c + "check/BindingWalk;)L" + c
                + "check/ValueOrigin;", Reading.NAMES, "asks the reading which projection, the"
                        + " longest first, is a position, as the descent would, and reads the"
                        + " names back up along them");
        row(out, c + "claims/UnreachableClaims", "claimedUnder", "(" + core + reads + "L" + c
                + "check/Symbols;L" + c + "check/DeclarationNewtypes;L" + c
                + "coverage/CoverageSites$Plan;L" + c + "coverage/NormalReturn;ZLjava/util/List;)V",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "codegen/BodyGen", "genExpr", "(" + core + "L" + c + "types/Type;)L" + c
                + "types/Type;", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "codegen/BodyGen", "walksInside", "(" + core + ")Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "check/RecordRules", "readFrom",
                "(" + core + "Ljava/util/Map;Ljava/util/Set;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/BlockReaches", "walk", "(" + core + "Ljava/util/Set;L" + c
                + "core/BlockReaches$Accumulator;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/Evaluated", "inOrder", "(" + core + ")Ljava/util/List;",
                Reading.STRUCTURE, EVALUATION);
        row(out, c + "core/WhatABodyReads", "binding",
                "(" + core + "Lsouther/compiler/types/BindingId;)Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "anyBinding", "(" + core + ")Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "anyOf", "(" + core + "Ljava/util/Set;)Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "madeOf", "(" + core + "Ljava/util/Set;)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "holds", "(" + core + "L" + c + "core/Core$Read;)Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "boundIn", "(" + core + "Ljava/util/Map;)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/WhatABodyReads", "readsIn",
                "(" + core + "Ljava/util/function/Consumer;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/GrowingFold", "adds", "(" + core + ")I",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/GrowingFold", "count", "(" + core + "Ljava/util/function/Predicate;[I)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "core/GrowingFold", "rewrite", "(" + core + "L" + c
                + "core/TheWalk;ZZ)" + core, Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/AnswerEmissionIndex", "walk", "(" + core + "L" + c
                + "coverage/CoverageSites$Plan;Ljava/util/Map;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/ArmEmissionIndex", "walk", "(" + core + "L" + c
                + "coverage/CoverageSites$Plan;Ljava/util/Map;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/Arrivals", "claim", "(" + core + "L" + c
                + "coverage/Arrivals;Ljava/util/Map;)V", Reading.STRUCTURE, EVALUATION);
        row(out, c + "coverage/ComparisonCatalog", "walk", "(" + core
                + "Ljava/lang/String;Ljava/util/Map;Ljava/util/Map;)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/ComparisonEmissionIndex", "walk", "(" + core + "L" + c
                + "coverage/CoverageSites$Plan;Ljava/util/Map;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/CoreStructure", "childrenOf", "(" + core + ")Ljava/util/List;",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/CoverageSites$Walk", "descend", "(" + core + "Z)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        // The comparisons of a helper's method, which is a tree that runs as a behavior's is.
        row(out, c + "coverage/CoverageSites$Walk", "comparisonsIn", "(" + core + "Z)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        // What carrying an arm's sibling costs, and whether the sibling reads its own arm's name.
        row(out, c + "coverage/CoverageSites$Walk", "nodesIn", "(" + core + ")I",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/CoverageSites$Walk", "reads", "(" + core + "L" + c
                + "types/BindingId;)Z", Reading.STRUCTURE, BINDINGS);
        row(out, c + "coverage/CoverageSites$Walk", "readsABindingOf", "(" + core + "L" + c
                + "types/BindingOwner;)Z", Reading.STRUCTURE, BINDINGS);
        // Whether a walk reads nothing a run is handed: the names it binds, and the names it reads
        // that it does not bind.
        row(out, c + "coverage/CoverageSites$Walk", "bindersIn", "(" + core
                + "Ljava/util/Set;)V", Reading.STRUCTURE, BINDINGS);
        row(out, c + "coverage/CoverageSites$Walk", "closedUnder", "(" + core
                + "Ljava/util/Set;)Z", Reading.STRUCTURE, BINDINGS);
        // Whether the order of the list a walk goes over is one the language leaves unspecified,
        // asked of the tree that runs.
        row(out, c + "coverage/CoverageSites$Walk", "listsWhatHasNoOrder", "(" + core + ")Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "check/PathReachability", "gatherPlaces", "(" + core + reads
                + "Ljava/util/Map;Ljava/util/Map;)V", Reading.EACH_SUBEXPRESSION, ASKS_EACH);
        // Whether an answer a body can come to is the same on every run, asked of the body a run
        // goes through.
        row(out, c + "coverage/CoverageSites$Walk", "sameOnEveryRun", "(" + core + ")Z",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/Methods", "collectCalls", "(" + core
                + "Ljava/util/Map;Ljava/util/Set;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "coverage/Methods", "callsIn", "(" + core + "L" + c
                + "types/ValueName$Helper;Ljava/util/List;)V", Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "flow/ValueArrivals", "fill", "(" + core + "L" + c + "flow/Naming;L" + c
                + "flow/ComparisonWays;Ljava/util/Map;)V", Reading.STRUCTURE, EVALUATION);
        row(out, c + "flow/ValueArrivals", "partsOf", "(" + core + ")Ljava/util/List;",
                Reading.STRUCTURE, EVALUATION);
        row(out, c + "flow/Witnessed", "positionOf", "(" + core
                + "Ljava/util/function/Function;)Ljava/util/List;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/ElementProjection$Reading", "steps", "(" + core + "L" + c
                + "types/BindingId;L" + c + "inputs/BindingTrail;)L" + c
                + "inputs/OnePerElement$ReadOff;", Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/ElementProjection$Reading", "given", "(" + core + "L" + c
                + "inputs/OnePerElement$ReadOff$Taken;L" + c + "inputs/BindingTrail;)" + core,
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/InputUses$Walk", "whole", "(" + core + reads + ")V",
                Reading.EACH_SUBEXPRESSION, ASKS_EACH);
        // Which behaviors a body calls, and where each argument stands in its input.
        row(out, c + "query/CallExampleSeeds", "collect", "(" + core
                + "Ljava/util/function/Predicate;Ljava/util/List;)V", Reading.EACH_SUBEXPRESSION,
                ASKS_EACH);
        row(out, c + "inputs/InputUses$Walk", "takenOff", "(" + core + reads + ")V",
                Reading.EACH_SUBEXPRESSION, ASKS_EACH);
        row(out, c + "inputs/InputUses$Walk", "fieldOf", "(" + core + ")" + core,
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/InputPath", "introducing", "(" + core + "L" + c
                + "inputs/BindingEnvironment;L" + c + "inputs/InputPath$OfAConstruction;)L" + c
                + "inputs/PathResolution;", Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/InputPath", "named", "(" + core + "L" + c
                + "inputs/BindingEnvironment;)L" + c + "inputs/PathResolution;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "inputs/InputPath", "through", "(" + core + "L" + c
                + "inputs/InputPath$Wanted;L" + c + "inputs/BindingEnvironment;)L" + c
                + "inputs/PathResolution;", Reading.NAMES, READS_THE_NAMES);
        row(out, c + "partition/AffineReading$1", "readsThrough",
                "(L" + CORE + "$FieldAccess;" + reads + ")Z", Reading.ONE_ACCESS, ONE);
        row(out, c + "partition/ComparisonAssessment", "readsAnswer", "(" + core + "L" + c
                + "types/BindingId;)Z", Reading.STRUCTURE, BINDINGS);
        row(out, c + "partition/ComparisonReadings", "walk", "(" + core + "L" + c
                + "partition/ComparisonReadings$Body;" + reads + "L" + c
                + "partition/ClosureApplications;L" + c
                + "partition/LiveFlow;Ljava/util/List;ZLjava/util/List;Ljava/util/List;L" + c
                + "partition/ConditionNumbering;)V", Reading.STRUCTURE, CHOICES_AND_CALLS);
        // The way to a call of a helper that calls itself, whether a call stands somewhere, and
        // whether a body builds a value: each looks for a choice, a call or a build.
        row(out, c + "partition/ComparisonReadings", "wayTo", "(" + core + core + reads + "L" + c
                + "partition/ComparisonReadings$Body;)L" + c + "partition/ComparisonReadings$Way;",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "partition/ComparisonReadings", "collectWritten", "(" + core + "L" + c
                + "partition/ComparisonReadings$Body;Ljava/util/Set;)V", Reading.STRUCTURE,
                "which comparisons of the model are written in a condition, which no name read is");
        row(out, c + "partition/ComparisonReadings", "holds", "(" + core + core + ")Z",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "partition/ComparisonReadings", "standsIn", "(" + core + core + ")Z",
                Reading.STRUCTURE, "finds one node under another by identity, which a"
                        + " projection's base is on");
        row(out, c + "partition/ComparisonReadings", "bindingsIn",
                "(" + core + "Ljava/util/Map;)V", Reading.STRUCTURE, BINDINGS);
        row(out, c + "partition/ComparisonReadings", "boundTo",
                "(" + core + "Ljava/util/Set;Ljava/util/Set;)V", Reading.STRUCTURE, BINDINGS);
        row(out, c + "check/ContainerSizesUnderAWitness", "names", "(" + core + ")V",
                Reading.STRUCTURE, BINDINGS);
        row(out, c + "check/ContainerSizesUnderAWitness", "mentions",
                "(" + core + "L" + c + "types/BindingId;)Z", Reading.STRUCTURE, BINDINGS);
        row(out, c + "partition/ComparisonReadings", "buildsAValue", "(" + core + ")Z",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "partition/GuardThresholds", "throughEachValue", "(" + core + reads + "L"
                + c + "check/Symbols;L" + c + "check/DeclarationNewtypes;L" + c
                + "inputs/ReadMeaning$WhereKept;L" + c + "coverage/Arrivals;Ljava/util/List;)V",
                Reading.STRUCTURE, BINDINGS);
        row(out, c + "inputs/InputReads", "answerAt", "(" + core + "L" + c + "check/Symbols;L"
                + c + "check/DeclarationNewtypes;)L" + c + "inputs/InputReads$AnAnswerAt;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "partition/LiveFlow", "walk", "(" + core + "Ljava/util/Set;)V",
                Reading.STRUCTURE, BINDINGS);
        row(out, c + "partition/MeaningsOfABodyReading", "walk", "(" + core + reads + ")V",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "partition/Pullback$1", "leafOf", "(" + core + reads + "L" + c
                + "check/AffineForms$Outcome$StoppedAt;)L" + c + "numeric/LinearForm;",
                Reading.NAMES, READS_THE_NAMES);
        row(out, c + "partition/Pullback$1", "readsThrough",
                "(L" + CORE + "$FieldAccess;" + reads + ")Z", Reading.ONE_ACCESS, ONE);
        row(out, c + "check/Clauses$ReadsOfAClause$1", "readsThrough",
                "(L" + CORE + "$FieldAccess;Ljava/util/Map;)Z", Reading.ONE_ACCESS, ONE);
        row(out, c + "inputs/ElementValue$Reader$Names", "readsThrough",
                "(L" + CORE + "$FieldAccess;Ljava/util/Map;)Z", Reading.ONE_ACCESS, ONE);
        row(out, c + "partition/Pullback", "underItsAccesses", "(L" + c + "inputs/Denotation;)L"
                + c + "inputs/Denotation;", Reading.NAMES, READS_THE_NAMES);
        row(out, c + "partition/Pullback", "aWayInto", "(L" + c + "inputs/Denotation;"
                + "Ljava/util/Set;)L" + c + "partition/Pullback$Inside;", Reading.STRUCTURE,
                CHOICES_AND_CALLS);
        row(out, c + "partition/Pullback", "readOnceForEveryValue", "(" + core + reads
                + "Ljava/util/Set;)Z", Reading.STRUCTURE, BINDINGS);
        row(out, c + "partition/DataOrigins", "originsOf",
                "(" + core + reads + "Ljava/util/Set;)Ljava/util/Set;", Reading.NAMES,
                READS_THE_NAMES);
        row(out, c + "partition/DataOrigins", "answeredBy",
                "(" + core + reads + "Ljava/util/Set;)Ljava/util/Set;", Reading.STRUCTURE,
                CHOICES_AND_CALLS);
        row(out, c + "partition/Pullback", "comparisonHolding",
                "(" + core + "L" + c + "core/Core$Read;)" + core, Reading.THE_TREE_THAT_RUNS, RUNS);
        row(out, c + "partition/Pullback", "leaveUnsaidWhatMayEndARunUnder",
                "(" + core + reads + "L" + c + "partition/Pullback$Bound;)V", Reading.STRUCTURE,
                "asks each node what it ends a run for, of the owner of that: a name read off a"
                        + " value ends none, so what a projection may end one for is what its"
                        + " base may");
        row(out, c + "partition/Pullback", "boundInside",
                "(" + core + "L" + c + "core/Core$Block;" + reads + "L" + c
                        + "partition/Pullback$Bound;)L" + c + "partition/Pullback$Bound;",
                Reading.STRUCTURE,
                "asks the parts of a call what the closure it is handed to is applied to: a"
                        + " name read off a value is read off what its base is, so a projection"
                        + " is what its base is");
        row(out, c + "partition/Pullback", "leaveUnsaidOverWhereItStands",
                "(" + core + reads + "L" + c + "partition/Pullback$Bound;)V", Reading.STRUCTURE,
                "asks a node where it stands, and goes down to its parts where it stands nowhere:"
                        + " a projection stands where its base does, and a base that stands"
                        + " nowhere is a name no place is named for");
        row(out, c + "check/OrderOfElements", "walk", "(" + core + "Ljava/util/Map;[Z[I)V",
                Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "check/WhatARunMayEndFor", "of", "(" + core + ")L" + c
                        + "check/WhatARunMayEndFor$Endings;", Reading.STRUCTURE,
                "asks each node what it ends a run for, an operator or a call: a name read off a"
                        + " value ends none, so what a projection may end one for is what its base"
                        + " may");
        row(out, c + "check/WhatARunMayEndFor", "endsNoneAndReadsNoNameBeneath",
                "(" + core + ")Z", Reading.STRUCTURE,
                "asks each node what it ends a run for and whether it reads a name, and goes down"
                        + " to its parts: a name read off a value ends none, so what a projection"
                        + " may end one for is what its base may");
        row(out, c + "check/WhatARunMayEndFor", "endsNoneBeneath", "(" + core + ")Z",
                Reading.STRUCTURE,
                "asks each node what it ends a run for, and goes down to its parts: a name read"
                        + " off a value ends none, so what a projection may end one for is what"
                        + " its base may");
        row(out, c + "check/WhatARunMayEndFor", "endsOnlyWhereItsAnswerHasNoPlace",
                "(" + core + ")Z", Reading.STRUCTURE,
                "asks a node what it ends a run for, and each part under it: a projection ends"
                        + " none beyond what its base does");
        row(out, c + "partition/NumbersOnTheWayToATotal", "betweenNoughtAndTheAnswer",
                "(" + core + "Z)Z", Reading.STRUCTURE,
                "asks each node outside the closures what it ends a run for, and goes down to its"
                        + " parts: a projection ends none beyond what its base does");
        row(out, c + "partition/NumbersOnTheWayToATotal", "readOffWhatItIsHanded",
                "(" + core + "Ljava/util/Set;)Z", Reading.STRUCTURE,
                "asks whether a value is a run of fields read off a name a closure is handed,"
                        + " with nothing between, which the base answers");
        row(out, c + "partition/AffineReading$WhatLiesBesideTheStop", "collectUnder",
                "(" + core + "Ljava/util/Set;)V", Reading.STRUCTURE,
                "records each node and goes down to its parts: a projection is held where its"
                        + " base is");
        row(out, c + "partition/Pullback", "divisionBy", "(" + core + core + ")" + core,
                Reading.STRUCTURE,
                "asks each node whether it is the quotient by a divisor, and goes down to its"
                        + " parts: a projection holds it where its base does");
        row(out, c + "check/WhatARunMayEndFor", "forEachWorkedOut", "(L" + c
                        + "core/Core$IfConstructed;Ljava/util/function/Consumer;)V",
                Reading.STRUCTURE,
                "hands the parts of an attempt to a reader, the operands of the construction it"
                        + " tests and its arms, and reads none of them: a projection among them is"
                        + " read as the reader it is handed to reads one");
        row(out, c + "partition/Pullback", "chosenField", "(" + core + reads + ")L" + c
                        + "partition/Pullback$ChosenField;", Reading.STRUCTURE,
                "takes the field accesses over the call of a walk one at a time, and asks of the"
                        + " call what its step answers: a projection over the call is a field"
                        + " taken of a field, which is no walk to ask it of, and it is not read");
        row(out, c + "partition/Pullback", "measuredByCases", "(L" + c + "inputs/Denotation;"
                + "Ljava/util/Map;)L" + c + "partition/Pullback$SizedByCases;", Reading.STRUCTURE,
                CHOICES_AND_CALLS);
        row(out, c + "partition/DecisionSubjects", "workedOut", "(" + core + reads
                + "Ljava/util/Set;)Ljava/lang/String;", Reading.NAMES,
                "writes a projection as the access it ends with, whose target is the projection one"
                        + " name shorter, so its names are written as the accesses they stand for");
        row(out, c + "partition/PredicateReadings", "walk", "(" + core + "Ljava/lang/String;L" + c
                + "inputs/InputReading;" + reads + "L" + c + "partition/LiveFlow;ZLjava/util/List;L"
                + c + "partition/RuleReachNumbering;Ljava/util/Set;L" + c
                + "partition/PredicateReadings$Builds;)V", Reading.STRUCTURE, CHOICES_AND_CALLS);
        row(out, c + "reading/CoverageRead", "descend", "(" + core + "L" + c
                + "reading/CoverageNaming;L" + c + "reading/Reach;Z)V",
                Reading.THE_TREE_THAT_RUNS, RUNS);
        return out;
    }

    private static void row(Map<String, Row> out, String owner, String name, String descriptor,
                            Reading reading, String why) {
        Row already = out.put(AMethod.of(owner, name, descriptor), new Row(reading, why));
        if (already != null) {
            throw new AssertionError(owner + "#" + name + descriptor + " is written down twice");
        }
    }
}
