package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Exposing;
import souther.compiler.check.ModuleUniverse;
import souther.compiler.check.Registry;
import souther.compiler.check.Resolve;
import souther.compiler.check.Scoping;
import souther.compiler.query.Front;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * The modules one set of published classes declares, read as the compiler reads them.
 *
 * <p>What a declaration means is the front end's answer and not something read off its text: which
 * declaration a name reaches, whether a name is a local binding or something declared elsewhere,
 * what a bare name an import brought in stands for. So a reader that has to compare two builds'
 * declarations reads both through this, and compares what comes back rather than what was written.
 *
 * <p>Everything here is the compiler's own: {@link ModuleReadback} puts the declarations back
 * together as source, {@link Exposing} reads what the import lines bring in, {@link Scoping} works
 * out what the names a module writes can mean, and {@link Resolve} answers them. What this adds is
 * only which modules to read — a module's declarations reach the modules they name, and those have
 * to be in sight for a name to be resolved against them. Which is the whole of what a universe is
 * asked ({@link ModuleUniverse}), so that is all this is on the other side of the seam.
 *
 * <p>Not the query layer, because there are two universes and a compilation has one. The classes an
 * answer brings are not on this compile's path and never will be; they are a second set of
 * declarations to be read the same way, which is what this is for.
 */
public final class PublishedUniverse {

    private final PublishedClasses classes;
    // What each module gave, as the one value a reading answers with. Three maps filled at one
    // statement apiece is three places to remember, and the fact they hold is one fact: this is
    // what reading that module came back with.
    private final Map<String, ReadableModule> read = new LinkedHashMap<>();
    private final Map<String, Read> resolved = new LinkedHashMap<>();
    private final Set<String> unreadable = new LinkedHashSet<>();
    // What was reached and gave no reading, told apart the way a universe tells them apart: a name
    // these classes carry and this compiler could not read is not a name they say nothing about,
    // and an import of the second is the importer's mistake while an import of the first is not.
    private final Map<String, ModuleUniverse.InSight> beyondReading = new LinkedHashMap<>();

    private PublishedUniverse(PublishedClasses classes) {
        this.classes = classes;
    }

    /** The universe those classes declare. Nothing is read until a module is asked for. */
    public static PublishedUniverse of(PublishedClasses classes) {
        return new PublishedUniverse(classes);
    }

    /**
     * {@code module} as the front end reads it, or null where these classes do not declare it or
     * this compiler cannot read what they published.
     *
     * <p>Read once. A module is resolved against every module its declarations reach, so asking for
     * one reads the ones it names — and the modules those name, since a type of an imported type is
     * reached the same way.
     */
    public Read resolved(String module) {
        Read already = resolved.get(module);
        if (already != null || unreadable.contains(module)) {
            return already;
        }
        readReaching(module);
        if (!read.containsKey(module)) {
            unreadable.add(module);
            return null;
        }
        ModuleUniverse universe = universe();
        Registry<Ast.Def> registry = declaredBy();
        for (String name : Set.copyOf(read.keySet())) {
            if (resolved.containsKey(name)) {
                continue;
            }
            Hir.Module hir = resolve(universe, registry, name);
            if (hir == null) {
                unreadable.add(name);
            } else {
                resolved.put(name, new Read(hir, read.get(name).injectedBehaviors()));
            }
        }
        return resolved.get(module);
    }

    /**
     * Whether these classes say anything at all about {@code module}, as against saying something
     * this compiler cannot read.
     *
     * <p>Asked of the classes rather than of what was read: a module whose declarations came back
     * unreadable is one these classes do carry, and a reader deciding what to say about it needs the
     * two apart. Nothing is published for a name is one thing to tell someone; what is published
     * cannot be read here is another.
     */
    public boolean declares(String module) {
        // The same question the readback answers with `SaysNothing`, asked of the same function: a
        // class of that name with no declarations on it is a class this compiler put nothing on, not
        // something it failed to read. Two spellings of it would come apart, and a reader would be
        // sent to look for a boundary revision that has nothing to do with it.
        return ModuleReadback.carry(module, classes);
    }

    /** Reads {@code module} and everything its declarations name, as far as these classes go. */
    private void readReaching(String module) {
        Deque<String> toRead = new ArrayDeque<>(Set.of(module));
        Set<String> tried = new LinkedHashSet<>(Set.of(module));
        while (!toRead.isEmpty()) {
            String name = toRead.removeFirst();
            if (read.containsKey(name) || unreadable.contains(name)) {
                continue;
            }
            // Which of the two a name is comes off the reading itself. It used to be asked again of
            // the classes afterwards, because a reading that failed answered null however it failed.
            Readback readback = ModuleReadback.read(name, classes);
            if (!(readback instanceof Readback.Ready(ReadableModule readable))) {
                unreadable.add(name);
                beyondReading.put(name, readback instanceof Readback.Unreadable
                        ? ModuleUniverse.InSight.UNREADABLE : ModuleUniverse.InSight.UNKNOWN);
                continue;
            }
            read.put(name, readable);
            // Which modules a module's declarations name, answered where the compiler answers it:
            // an import line names one, and so does a type or a behavior written with a qualifier,
            // which needs no import at all.
            for (String reaches : Front.reaches(readable.module()).keySet()) {
                if (tried.add(reaches)) {
                    toRead.addLast(reaches);
                }
            }
        }
    }

    /**
     * A module as the front end reads it, with what its declarations do not say.
     *
     * <p>Which behaviors are left to be injected is not written in a declaration and does not
     * survive as source, so it travels beside the module ({@link ReadableModule}). It decides
     * whether an implementation may be supplied for a behavior at all, which is as much a fact about
     * a crossing as the behavior's signature is — so it travels this far too, rather than being
     * dropped where a reading turns into declarations.
     */
    public record Read(Hir.Module module, Set<String> injectedBehaviors) {}

    /**
     * What was read, as the universe a module is resolved against.
     *
     * <p>Nothing is worked out here. A module that came back readable came back indexed — which
     * declarations it has is settled while it is read, and a set of declarations one module may not
     * have is an artifact this compiler will not read, said as that. So a module is in sight with
     * what it declares, or it is one of the two kinds of absence, and there is no third thing that
     * can go wrong at the moment a universe is assembled.
     */
    private ModuleUniverse universe() {
        Map<String, ModuleUniverse.InSight> modules = new LinkedHashMap<>(beyondReading);
        for (Map.Entry<String, ReadableModule> each : read.entrySet()) {
            modules.put(each.getKey(), new ModuleUniverse.InSight.Read(
                    each.getValue().module(), each.getValue().declarations()));
        }
        return new ModuleUniverse.OfWhatIsRead(modules);
    }

    /**
     * What resolution reads other modules by: the declarations each reading settled, and nothing
     * worked out again.
     *
     * <p>Built from the same readings the universe is built from, so what a scope says a module
     * declares and what resolution finds there are one answer rather than two that happen to agree.
     */
    private Registry<Ast.Def> declaredBy() {
        Map<String, Map<String, Ast.Def>> declared = new LinkedHashMap<>();
        Map<String, Set<String>> exposed = new LinkedHashMap<>();
        for (Map.Entry<String, ReadableModule> each : read.entrySet()) {
            declared.put(each.getKey(), each.getValue().declarations());
            exposed.put(each.getKey(), Registry.baseNames(each.getValue().module().exposing()));
        }
        return Registry.ofRead(declared, exposed);
    }

    /**
     * {@code module} with every name it writes answered, or null where a name could not be.
     *
     * <p>The scope is {@link Scoping}'s and not this class's. What an import line brought in, what a
     * bare type name denotes, what a bare name in the value namespace reaches — a reader that worked
     * any of them out for itself would be a second answer to a question a compilation already
     * answers, and the two came to differ: a model compiled in the project that wrote it and refused
     * to be imported anywhere else.
     *
     * <p>A refusal is this reader taking the module as one it cannot read. Nothing is said about it:
     * a published module was compiled before it was published, so an import line that cannot do its
     * job here says something about what these classes carry rather than about what an author wrote,
     * and whoever asked is the one to decide what that means.
     */
    private Hir.Module resolve(ModuleUniverse universe, Registry<Ast.Def> registry, String module) {
        if (!(universe.module(module) instanceof ModuleUniverse.InSight.Read read)) {
            return null;
        }
        Scoping.Scoped scoped = Scoping.of(universe,
                new Scoping.Subject(read, this.read.get(module).libraryNames()));
        if (!scoped.refused().isEmpty()) {
            return null;
        }
        Resolve.Resolution resolution = Resolve.resolving(read.module(),
                scoped.writtenSymbols(registry), scoped.values());
        return resolution.unresolved().isEmpty() ? resolution.module() : null;
    }
}
