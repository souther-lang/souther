package souther.bench;

import org.junit.jupiter.api.Test;

import java.io.IOException;
import java.lang.classfile.Attributes;
import java.lang.classfile.ClassFile;
import java.lang.classfile.ClassModel;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * The partitioning stage reads what a position is; it never works it out again underneath.
 *
 * <p>What a value is made of has one answer, and the stage had it four ways over: from the reading
 * of a position, from the declaration through its field types, from a collection constructor taken
 * apart by hand, and from a walk reaching through the names a value is written under. Four readings
 * of one fact agree wherever they happen to stop at the same depth and part everywhere else — at a
 * sum, at a name over a name, inside a container — and each parting was a defect somebody found
 * separately.
 *
 * <p><b>So this is about reachability and not about a vocabulary.</b> A rule naming the ways
 * anybody had written it down so far would be passed by the next one written another way, and that
 * is the failure this exists after rather than a hypothetical: the walk it removed reached the
 * declaration through an accessor no earlier rule watched. What is checked is that no path from the
 * stage arrives at raw structure at all, however many methods it goes through and whatever those
 * methods return. A helper handing back a {@code boolean} hides nothing here, because what is
 * followed is the call and not the answer.
 *
 * <p><b>What counts as raw structure is the types' own statement.</b> {@link
 * souther.compiler.types.Type.Leaf} says it holds no type inside it and {@link
 * souther.compiler.types.Type.Compound} says it is built out of others, so taking a compound apart
 * is reading structure and reading the name off a {@code Ref} is not — a {@code Ref} has no
 * structure to read, which is what makes it a leaf. {@link souther.compiler.ast.Hir.Def} permits
 * the declarations, so reaching one of those is reading what a module wrote. Both sets come from
 * the sealed hierarchies rather than from a list here, and a constructor added to either joins them
 * without anybody remembering to.
 *
 * <p><b>The stage stops at an authority, and the authorities are the point.</b> Each is a place
 * that owns a question, reads whatever raw material that question needs, and hands back an answer.
 * The table below is not a list of methods allowed to reach past the boundary — it is why the stage
 * does not need to look past it. A method reaching raw structure that no authority answers for is a
 * second reading of something already decided, whatever it is called.
 */
class PartitionReadsAPositionRatherThanReinterpretingItTest {

    /** The stage this is about: where a row for a coverage item is composed. */
    private static final String STAGE = "souther.compiler.partition.";

    /** What a declaration is, as {@code Hir.Def} permits them. */
    private static final String DECLARATION = "souther.compiler.ast.Hir$Def";

    /** What is built out of types, as {@code Type} divides itself. */
    private static final String COMPOUND = "souther.compiler.types.Type$Compound";

    /** Whether a walk stops at an authority or carries on through it. */
    enum Traversal {

        /**
         * The answer is complete before anything of the caller's runs, so what the authority reads
         * to make it is its own business and the walk stops here.
         */
        OPAQUE,

        /**
         * The owner of the question, walked through all the same. What it answers with is composed
         * by something the caller handed it, so a reading the caller wrote is reached from here —
         * and stopping at this boundary would put a caller's own walk on the far side of it.
         */
        TRANSPARENT
    }

    /**
     * A place that owns a question, and what a walk does when it arrives.
     *
     * @param question what it answers, in the words the answer is about. A place that cannot be
     *                 given one that some other authority does not already answer is not an
     *                 authority: it is a second reading under another name
     * @param owns     the class, or the one method of it, that answers. A class holding several
     *                 unrelated questions is named by the method, because that is the size of the
     *                 owner and not because the rest of the class is being excused
     */
    record Authority(String question, String owns, Traversal traversal) {

        /** Whether this answers for {@code at}, named with or without what it takes and returns. */
        boolean answersFor(String at) {
            String named = at.contains("(") ? at.substring(0, at.indexOf('(')) : at;
            String owner = named.substring(0, named.indexOf('#'));
            return owns.contains("#")
                    ? named.equals(owns)
                    : owner.equals(owns) || owner.startsWith(owns + "$");
        }
    }

    /**
     * Why the stage does not have to look past each of these.
     *
     * <p>A place earns an entry by answering four things. It has a question of its own, rather than
     * giving another authority's answer a second name. What it hands back is that answer, never the
     * raw material — a type as the subject of a question is fine, a child type or a declaration
     * handed out is not. It finishes before anything of the caller's runs. And it is the lowest
     * owner: a facade or a switch that hands the decision on is walked through to whatever makes
     * it.
     */
    private static final List<Authority> AUTHORITIES = List.of(
            // What a position is, and how it is written. The one this stage exists on top of.
            new Authority("what a position is, with the names it is written under off",
                    "souther.compiler.check.TypeView", Traversal.OPAQUE),
            new Authority("what the rules written on a record leave its fields able to hold",
                    "souther.compiler.check.FieldDomains", Traversal.OPAQUE),
            new Authority("which conjuncts are written on each of the names a value wears",
                    "souther.compiler.check.DeclaredClauses", Traversal.OPAQUE),
            new Authority("which ends a declaration writes on the values of a type",
                    "souther.compiler.check.DeclaredBounds", Traversal.OPAQUE),
            new Authority("which binding each field of a declaration introduces inside its own"
                            + " invariant",
                    "souther.compiler.check.TypeOps#fieldBindings", Traversal.OPAQUE),
            new Authority("what carries the values of a type, and in what order",
                    "souther.compiler.check.Carrier", Traversal.OPAQUE),
            new Authority("whether reading a field reaches another location",
                    "souther.compiler.check.Location", Traversal.OPAQUE),
            new Authority("what there is to count about a value",
                    "souther.compiler.check.NumericMeasures", Traversal.OPAQUE),
            new Authority("which distinctions the type at a position states",
                    "souther.compiler.inputs.Distinctions", Traversal.OPAQUE),
            new Authority("what reaches each position of a behavior's inputs, read once",
                    "souther.compiler.inputs.InputDomain", Traversal.OPAQUE),
            new Authority("what a name in the tree denotes where the reader stands",
                    "souther.compiler.inputs.InputReads", Traversal.OPAQUE),
            new Authority("which number of an input an expression names",
                    "souther.compiler.inputs.InputNumber", Traversal.OPAQUE),
            new Authority("which number a comparison draws which line on",
                    "souther.compiler.inputs.ComparedNumber", Traversal.OPAQUE),
            new Authority("whether an operation and a position make one term of a number taken of"
                            + " a value",
                    "souther.compiler.inputs.NumericTerm$TakenOf", Traversal.OPAQUE),
            new Authority("how a type is written where an author reads it",
                    "souther.compiler.types.Type#show", Traversal.OPAQUE),

            // Owners all the same, walked through. Neither can stand as a boundary: what one
            // answers with is composed by a reading the caller wrote, and the other hands its
            // decision to whichever term it is about — so a stop at either would leave the walk
            // this checks on the far side of it.
            new Authority("what affine form an expression composes",
                    "souther.compiler.check.AffineForms", Traversal.TRANSPARENT),
            new Authority("what a term about a number comes to at another position",
                    "souther.compiler.inputs.NumericTerm", Traversal.TRANSPARENT));

    /**
     * No path from the stage reaches raw structure without an authority answering for it.
     *
     * <p>Both what a method's own code does and what it calls, to any depth. A place that reads
     * structure and hands back a word about it is on the path like any other: what makes the
     * difference is whether some authority owns the question, not what the answer is made of.
     */
    @Test
    void nothingInTheStageReadsStructureThatNoAuthorityAnswersFor() throws IOException {
        Structure world = Structure.read();

        assertFalse(world.observers().isEmpty(),
                "no reading of raw structure was found anywhere, so this asserts nothing about the"
                        + " stage: the walk or the sinks are wrong rather than the compiler clean");
        assertFalse(world.stageMethods().isEmpty(),
                "the stage has no compiled methods, so nothing was checked");

        assertEquals(List.of(), world.bypasses(),
                "a path from the partitioning stage to raw structure that no authority answers"
                        + " for. Either the question it is asking has an owner and it should ask"
                        + " there, or it is a second reading of something a reading already"
                        + " decided");
    }

    /**
     * Every authority is one the stage actually reaches.
     *
     * <p>The other way round, and the half that keeps this from becoming a list. An entry nothing
     * arrives at is a rule about a boundary that is not there — either the reader that needed it
     * has gone, and the entry with it, or the walk stopped reaching it and what this checks has
     * quietly narrowed.
     */
    @Test
    void everyAuthorityIsOneTheStageArrivesAt() throws IOException {
        Structure world = Structure.read();
        List<String> unreached = new ArrayList<>();
        for (Authority each : AUTHORITIES) {
            if (world.reached().stream().noneMatch(each::answersFor)) {
                unreached.add(each.owns());
            }
        }
        assertEquals(List.of(), unreached,
                "an authority nothing in the stage arrives at, which is a rule about a boundary"
                        + " that is not there");
    }

    /**
     * What the compiled classes hold, and what follows from it.
     *
     * @param observers  the methods whose own code reads raw structure
     * @param stageMethods every compiled method of the stage
     * @param reached    what the stage calls, one step out
     * @param bypasses   the stage's methods that reach raw structure with no authority between,
     *                   each with the path that gets there
     */
    record Structure(Set<String> observers, Set<String> stageMethods, Set<String> reached,
                     List<String> bypasses) {

        static Structure read() throws IOException {
            Map<String, ClassModel> models = new LinkedHashMap<>();
            for (Path each : Reactor.classes()) {
                ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
                models.put(model.thisClass().asInternalName().replace('/', '.'), model);
            }
            Set<String> declarations = descendantsOf(models, DECLARATION);
            Map<String, Set<String>> apart = componentsHoldingTypes(models,
                    descendantsOf(models, COMPOUND));

            Set<String> observers = new LinkedHashSet<>();
            Set<String> stage = new LinkedHashSet<>();
            Set<String> reached = new LinkedHashSet<>();
            Map<String, Set<String>> callersOf = new LinkedHashMap<>();
            Map<String, String> why = new LinkedHashMap<>();
            for (Compiled.Site site : Compiled.sites()) {
                if (site.from().startsWith(STAGE)) {
                    stage.add(site.at());
                    reached.add(site.owner() + "#" + site.member());
                }
                callersOf.computeIfAbsent(site.owner() + "#" + site.member(),
                        k -> new LinkedHashSet<>()).add(site.at());
                String read = observation(site, declarations, apart);
                if (read != null) {
                    observers.add(site.at());
                    why.putIfAbsent(site.at(), read);
                }
            }

            // Backwards from every reading of raw structure, stopping where an authority answers.
            // A method inside one is not carrying the reading outwards — it is making the answer.
            Map<String, String> through = new LinkedHashMap<>();
            Deque<String> queue = new ArrayDeque<>();
            for (String at : observers) {
                if (!answeredBy(at, Traversal.OPAQUE) && through.putIfAbsent(at, why.get(at)) == null) {
                    queue.add(at);
                }
            }
            while (!queue.isEmpty()) {
                String at = queue.poll();
                for (String caller : callersOf.getOrDefault(at.substring(0, at.indexOf('(')),
                        Set.of())) {
                    if (answeredBy(caller, Traversal.OPAQUE)
                            || through.putIfAbsent(caller, at) != null) {
                        continue;
                    }
                    queue.add(caller);
                }
            }

            List<String> bypasses = new ArrayList<>();
            for (String at : stage) {
                if (through.containsKey(at)) {
                    bypasses.add(at.substring(STAGE.length()) + "  ->  " + pathFrom(at, through));
                }
            }
            bypasses.sort(null);
            return new Structure(observers, stage, reached, bypasses);
        }

        /** How the reading is arrived at from here, for a reader who has to go and look. */
        private static String pathFrom(String at, Map<String, String> through) {
            List<String> path = new ArrayList<>();
            String walk = at;
            Set<String> seen = new LinkedHashSet<>();
            while (walk != null && seen.add(walk) && path.size() < 8) {
                String next = through.get(walk);
                if (next == null || !next.contains("#")) {
                    path.add(next == null ? "?" : next);
                    break;
                }
                path.add(next.substring(0, next.indexOf('(')));
                walk = next;
            }
            return String.join(" -> ", path);
        }

        private static boolean answeredBy(String at, Traversal how) {
            return AUTHORITIES.stream()
                    .anyMatch(each -> each.traversal() == how && each.answersFor(at));
        }
    }

    /** What this site reads of raw structure, or null where it reads none. */
    private static String observation(Compiled.Site site, Set<String> declarations,
                                      Map<String, Set<String>> apart) {
        if (declarations.contains(site.owner())) {
            return "reaches a declaration: " + site.owner() + "#" + site.member();
        }
        if (site.owner().equals("souther.compiler.check.Symbols")
                && site.member().equals("declaredNode")) {
            return "asks what a name declares";
        }
        if (!apart.containsKey(site.owner())) {
            return null;
        }
        return switch (site.how()) {
            case ASKS, NAMES -> "asks which compound a type is: " + site.owner();
            case CALLS, REFERS -> apart.get(site.owner()).contains(site.member())
                    ? "takes a compound apart: " + site.owner() + "#" + site.member() : null;
            // Making one is not reading one, and a field of a compound holds no type to read.
            case MAKES, READS -> null;
        };
    }

    /** Every class of this repository that is a {@code root}, root included. */
    private static Set<String> descendantsOf(Map<String, ClassModel> models, String root) {
        Set<String> found = new LinkedHashSet<>(Set.of(root));
        boolean grew = true;
        while (grew) {
            grew = false;
            for (var entry : models.entrySet()) {
                if (found.contains(entry.getKey())) {
                    continue;
                }
                List<String> above = new ArrayList<>();
                entry.getValue().superclass()
                        .ifPresent(each -> above.add(each.asInternalName().replace('/', '.')));
                entry.getValue().interfaces()
                        .forEach(each -> above.add(each.asInternalName().replace('/', '.')));
                if (above.stream().anyMatch(found::contains)) {
                    found.add(entry.getKey());
                    grew = true;
                }
            }
        }
        return found;
    }

    /**
     * For each compound, the components of it that are made of types.
     *
     * <p>Off the generic signature where there is one: a list of types erases to a list, and a rule
     * written over descriptors alone would not see what a tuple or a function holds.
     */
    private static Map<String, Set<String>> componentsHoldingTypes(Map<String, ClassModel> models,
                                                                   Set<String> compounds) {
        Map<String, Set<String>> found = new LinkedHashMap<>();
        for (String each : compounds) {
            ClassModel model = models.get(each);
            if (model == null) {
                continue;
            }
            Set<String> holding = new LinkedHashSet<>();
            model.findAttribute(Attributes.record()).ifPresent(record -> {
                for (var component : record.components()) {
                    String written = component.findAttribute(Attributes.signature())
                            .map(signature -> signature.signature().stringValue())
                            .orElse(component.descriptor().stringValue());
                    if (written.contains("Lsouther/compiler/types/Type;")) {
                        holding.add(component.name().stringValue());
                    }
                }
            });
            found.put(each, holding);
        }
        return found;
    }
}
