package souther.bench;

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

/**
 * Where a stage's calls arrive at raw structure, and what answers for them on the way.
 *
 * <p>What it reads and which classes it reads are two things. The rule about this compiler names
 * the partitioning stage and the compiler's own sums; a check of the reading itself hands it code
 * written to be read, and neither is a copy of the other. A second walk written for the second
 * purpose would be a check of the copy.
 *
 * <p>Everything about the vocabulary is an argument for the same reason. What a declaration is and
 * what is built out of types are stated by the sums the caller names, so the walk derives both from
 * the class files rather than knowing either — and a caller can therefore hand it a sum of its own
 * and see what the walk makes of it.
 */
final class PositionReadings {

    private PositionReadings() {}

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
     * What the walk is over.
     *
     * @param classes     the compiled classes to read
     * @param stage       the package whose methods are held to the rule, by name prefix
     * @param declaration the sum whose cases are what a module wrote
     * @param lookup      the one method that answers what a name declares, or null where the
     *                    vocabulary has none
     * @param compound    the sum whose cases are built out of types
     * @param held        the descriptor of what a compound's components hold, so that a component
     *                    made of them is told from one that is not
     * @param authorities what answers for a reading, and what a walk does at each
     */
    record Over(List<Path> classes, String stage, String declaration, String lookup,
                String compound, String held, List<Authority> authorities) {}

    /**
     * What the classes hold and what follows from it.
     *
     * @param observers the methods whose own code reads raw structure
     * @param inTheStage every compiled method of the stage
     * @param reached   what the stage calls, one step out
     * @param bypassing the stage's methods that reach raw structure with no authority between
     * @param bypasses  the same, each with the path that gets there, for a reader to go and look
     */
    record Reading(Set<String> observers, Set<String> inTheStage, Set<String> reached,
                   List<String> bypassing, List<String> bypasses) {

        /** Which methods those are, by name alone, which is what a claim about them is written in. */
        List<String> named() {
            List<String> out = new ArrayList<>();
            for (String each : bypassing) {
                out.add(each.substring(each.indexOf('#') + 1, each.indexOf('(')));
            }
            out.sort(null);
            return out;
        }
    }

    static Reading of(Over over) throws IOException {
        Map<String, ClassModel> models = new LinkedHashMap<>();
        for (Path each : over.classes()) {
            ClassModel model = ClassFile.of().parse(Files.readAllBytes(each));
            models.put(model.thisClass().asInternalName().replace('/', '.'), model);
        }
        Set<String> declarations = descendantsOf(models, over.declaration());
        Map<String, Set<String>> apart =
                componentsHolding(models, descendantsOf(models, over.compound()), over.held());

        Set<String> observers = new LinkedHashSet<>();
        Set<String> stage = new LinkedHashSet<>();
        Set<String> reached = new LinkedHashSet<>();
        Map<String, Set<String>> callersOf = new LinkedHashMap<>();
        Map<String, String> why = new LinkedHashMap<>();
        for (Compiled.Site site : Compiled.sitesIn(over.classes())) {
            if (site.from().startsWith(over.stage())) {
                stage.add(site.at());
                reached.add(site.owner() + "#" + site.member());
            }
            callersOf.computeIfAbsent(site.owner() + "#" + site.member(),
                    k -> new LinkedHashSet<>()).add(site.at());
            String read = observation(site, declarations, apart, over.lookup());
            if (read != null) {
                observers.add(site.at());
                why.putIfAbsent(site.at(), read);
            }
        }

        // Backwards from every reading of raw structure, stopping where an authority answers. A
        // method inside one is not carrying the reading outwards — it is making the answer.
        Map<String, String> through = new LinkedHashMap<>();
        Deque<String> queue = new ArrayDeque<>();
        for (String at : observers) {
            if (!stops(over, at) && through.putIfAbsent(at, why.get(at)) == null) {
                queue.add(at);
            }
        }
        while (!queue.isEmpty()) {
            String at = queue.poll();
            for (String caller
                    : callersOf.getOrDefault(at.substring(0, at.indexOf('(')), Set.of())) {
                if (stops(over, caller) || through.putIfAbsent(caller, at) != null) {
                    continue;
                }
                queue.add(caller);
            }
        }

        List<String> bypassing = new ArrayList<>();
        List<String> bypasses = new ArrayList<>();
        for (String at : stage) {
            if (through.containsKey(at)) {
                bypassing.add(at);
                bypasses.add(at.substring(over.stage().length()) + "  ->  " + pathFrom(at, through));
            }
        }
        bypassing.sort(null);
        bypasses.sort(null);
        return new Reading(observers, stage, reached, bypassing, bypasses);
    }

    /** The authorities of {@code over} nothing in the stage arrives at. */
    static List<String> unreached(Over over, Reading reading) {
        List<String> out = new ArrayList<>();
        for (Authority each : over.authorities()) {
            if (reading.reached().stream().noneMatch(each::answersFor)) {
                out.add(each.owns());
            }
        }
        return out;
    }

    private static boolean stops(Over over, String at) {
        return over.authorities().stream()
                .anyMatch(each -> each.traversal() == Traversal.OPAQUE && each.answersFor(at));
    }

    /** How the reading is arrived at from here, for a reader who has to go and look. */
    private static String pathFrom(String at, Map<String, String> through) {
        List<String> path = new ArrayList<>();
        String walk = at;
        Set<String> seen = new LinkedHashSet<>();
        while (walk != null && seen.add(walk) && path.size() < 8) {
            String next = through.get(walk);
            // The end of a path is why it is one, which is a sentence rather than a method — and a
            // sentence naming the member it is about has a `#` in it like any other.
            if (next == null || !next.contains("(")) {
                path.add(next == null ? "?" : next);
                break;
            }
            path.add(next.substring(0, next.indexOf('(')));
            walk = next;
        }
        return String.join(" -> ", path);
    }

    /** What this site reads of raw structure, or null where it reads none. */
    private static String observation(Compiled.Site site, Set<String> declarations,
                                      Map<String, Set<String>> apart, String lookup) {
        if (declarations.contains(site.owner())) {
            return "reaches a declaration: " + site.owner() + "#" + site.member();
        }
        if (lookup != null && (site.owner() + "#" + site.member()).equals(lookup)) {
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

    /** Every class among {@code models} that is a {@code root}, root included. */
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
     * For each compound, the components of it that hold {@code held}.
     *
     * <p>Off the generic signature where there is one: a list of them erases to a list, and a rule
     * written over descriptors alone would not see what a tuple or a function holds.
     */
    private static Map<String, Set<String>> componentsHolding(Map<String, ClassModel> models,
                                                              Set<String> compounds, String held) {
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
                    if (written.contains(held)) {
                        holding.add(component.name().stringValue());
                    }
                }
            });
            found.put(each, holding);
        }
        return found;
    }
}
