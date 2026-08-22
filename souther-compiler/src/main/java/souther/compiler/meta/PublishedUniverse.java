package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Exposing;
import souther.compiler.check.BehaviorImplementation;
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
    /**
     * What reading each module off these classes came back with — the one record of it, and what
     * everything else here is derived from.
     *
     * <p>One map and not several. What a module gave used to be kept in four: the ones that were
     * read, the ones that were resolved, the names of the ones that were not, and what a universe
     * was to say about those. They hold one fact between them, and holding it four times is four
     * places to write it and three chances to write it in one of them and not the rest — which is
     * what let a reading that had a reason arrive at a caller as a name in a set.
     */
    private final Map<String, Readback<ReadableModule>> readbacks = new LinkedHashMap<>();
    /**
     * The same modules with their names answered, derived from {@link #readbacks} and from nothing
     * else.
     *
     * <p>A cache and not a second record: a module that could not be read is not resolved, and what
     * this holds for one is what the reading already said, restated as the answer of this stage
     * ({@link Readback.NotReady#asTheAnswerOf}). Nothing is learned here that the reading did not
     * have.
     *
     * <p>Both maps are written once per name. A module is read whole — everything its declarations
     * reach is read with it — so what it resolves against does not grow between one caller asking
     * for it and the next, and an entry replaced later would be this class answering two things
     * about one module over the life of one universe.
     */
    private final Map<String, Readback<Read>> resolutions = new LinkedHashMap<>();

    private PublishedUniverse(PublishedClasses classes) {
        this.classes = classes;
    }

    /** The universe those classes declare. Nothing is read until a module is asked for. */
    public static PublishedUniverse of(PublishedClasses classes) {
        return new PublishedUniverse(classes);
    }

    /**
     * {@code module} as the front end reads it, in the same three states reading one off these
     * classes answers with.
     *
     * <p>A reading that got no further than the classes is answered as the reading found it, and
     * one that got as far as this stage and stopped says why here. Answered with a null instead,
     * every reason found on this side of the seam — an import line naming a module these classes do
     * not carry, one asking for a name a module does not declare, a spelling two lines both bring
     * in — had nowhere to be said, and a caller could tell the states apart only by asking the
     * classes something else and reading the answer as a reason.
     *
     * <p>Read once. A module is resolved against every module its declarations reach, so asking for
     * one reads the ones it names — and the modules those name, since a type of an imported type is
     * reached the same way.
     */
    public Readback<Read> resolved(String module) {
        Readback<Read> already = resolutions.get(module);
        if (already != null) {
            return already;
        }
        readReaching(module);
        ModuleUniverse universe = universe();
        Registry<Ast.Def> registry = declaredBy();
        // Every module that has been read and not yet resolved, and not this one alone: they are
        // resolved against each other, and one left out would be a neighbour whose declarations
        // this answers questions about without having answered its own names.
        for (Map.Entry<String, Readback<ReadableModule>> each
                : Map.copyOf(readbacks).entrySet()) {
            if (resolutions.containsKey(each.getKey())) {
                continue;   // written once: what was answered for a name stays that answer
            }
            resolutions.put(each.getKey(),
                    resolutionOf(universe, registry, each.getKey(), each.getValue()));
        }
        return resolutions.get(module);
    }

    /** Reads {@code module} and everything its declarations name, as far as these classes go. */
    private void readReaching(String module) {
        Deque<String> toRead = new ArrayDeque<>(Set.of(module));
        Set<String> tried = new LinkedHashSet<>(Set.of(module));
        while (!toRead.isEmpty()) {
            String name = toRead.removeFirst();
            if (readbacks.containsKey(name)) {
                continue;
            }
            // What the reading answered, kept as it answered it. Which of the states a name is in
            // used to be asked again of the classes afterwards, because a reading that failed
            // answered null however it failed.
            Readback<ReadableModule> readback = ModuleReadback.read(name, classes);
            readbacks.put(name, readback);
            if (!(readback instanceof Readback.Ready<ReadableModule>(ReadableModule readable))) {
                continue;
            }
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
     * <p>Where a behavior's body comes from is not written in a declaration and does not survive as
     * source, so it travels beside the module ({@link ReadableModule}). It decides whether an
     * implementation may be supplied for a behavior at all, which is as much a fact about a crossing
     * as the behavior's signature is — so it travels this far too, rather than being dropped where a
     * reading turns into declarations.
     */
    public record Read(Hir.Module module,
                       Map<String, BehaviorImplementation> behaviorImplementations) {

        /** The behaviors of it Java supplies, read off the states. */
        public Set<String> injectedBehaviors() {
            Set<String> injected = new java.util.LinkedHashSet<>();
            behaviorImplementations.forEach((name, implementation) -> {
                if (implementation.isInjectionTarget()) {
                    injected.add(name);
                }
            });
            return injected;
        }
    }

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
        Map<String, ModuleUniverse.InSight> modules = new LinkedHashMap<>();
        // Read off the readings and nothing else. What a universe says about a name is which of the
        // three a reading of it came back as, and the two kinds of absence are told apart the way a
        // universe tells them apart: a name these classes carry and this compiler could not read is
        // not a name they say nothing about, and an import of the second is the importer's mistake
        // while an import of the first is not.
        readbacks.forEach((name, readback) -> modules.put(name, switch (readback) {
            case Readback.Ready<ReadableModule>(ReadableModule readable) ->
                    ModuleUniverse.InSight.Read.of(readable.module(), declaredBy(readable));
            case Readback.NotReady.Unreadable<ReadableModule> _ ->
                    ModuleUniverse.InSight.UNREADABLE;
            case Readback.NotReady.SaysNothing<ReadableModule> _ -> ModuleUniverse.InSight.UNKNOWN;
        }));
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
        Map<String, Registry.Declared<Ast.Def>> declared = new LinkedHashMap<>();
        readbacks.forEach((name, readback) -> {
            if (readback instanceof Readback.Ready<ReadableModule>(ReadableModule readable)) {
                declared.put(name, declaredBy(readable));
            }
        });
        return Registry.ofRead(declared);
    }

    /** What a registry has under one reading's name. The {@code exposing} list is read here, on
     *  this side of the seam, and by nothing downstream of it. */
    private static Registry.Declared<Ast.Def> declaredBy(ReadableModule readable) {
        return new Registry.Declared<>(readable.declarations(),
                Registry.baseNames(readable.module().exposing()));
    }

    /**
     * What this stage answers for one module, given what reading it answered.
     *
     * <p>A module the reading could not hand over is answered with what the reading said, as this
     * stage's answer. The reason travels rather than being worked out again: a caller that was
     * handed nothing here used to ask the classes whether they carry the name at all and read that
     * as the reason, which says only which of two coarse things happened and says it from a
     * question that has nothing to do with the reading.
     */
    private Readback<Read> resolutionOf(ModuleUniverse universe, Registry<Ast.Def> registry,
                                        String module, Readback<ReadableModule> readback) {
        return switch (readback) {
            case Readback.NotReady<ReadableModule> notRead -> notRead.asTheAnswerOf();
            case Readback.Ready<ReadableModule>(ReadableModule readable) ->
                    resolve(universe, registry, module, readable);
        };
    }

    /**
     * {@code module} with every name it writes answered, or why none of them could be.
     *
     * <p>The scope is {@link Scoping}'s and not this class's. What an import line brought in, what a
     * bare type name denotes, what a bare name in the value namespace reaches — a reader that worked
     * any of them out for itself would be a second answer to a question a compilation already
     * answers, and the two came to differ: a model compiled in the project that wrote it and refused
     * to be imported anywhere else.
     *
     * <p>A refusal is this reader taking the module as one it cannot read, and saying why. A
     * published module was compiled before it was published, so an import line that cannot do its
     * job here is a fact about what these classes carry rather than about what an author wrote —
     * which is what makes it one of the facts a reading answers with, told to whoever asked in the
     * words the reading uses for every other one. Left as nothing at all, which reason a reader was
     * given followed from which side of this seam the refusal was found on: the lines that name the
     * standard library are read where no other module has to be in sight, so those had a name and
     * the rest did not.
     */
    private Readback<Read> resolve(ModuleUniverse universe, Registry<Ast.Def> registry,
                                   String module, ReadableModule readable) {
        // The module itself comes from the reading this universe was built out of, and not from
        // what the universe answers about it: a neighbour is settled facts, and only the module
        // being scoped is read from.
        Scoping.Scoped scoped = Scoping.of(universe, new Scoping.Subject(readable.module(),
                declaredBy(readable), readable.libraryClaims()));
        if (!scoped.refused().isEmpty()) {
            return new Readback.NotReady.Unreadable<>(module,
                    ScopeRefusals.of(scoped.refused()));
        }
        Resolve.Resolution resolution = Resolve.resolving(readable.module(),
                scoped.meanings().writtenSymbols(registry), scoped.values());
        if (!resolution.unresolved().isEmpty()) {
            // What resolution has for each of them is a report, written for an author holding the
            // file and quoting the line — a line of the text this reading assembled. So what
            // crosses is that they did not resolve, and nothing taken out of a diagnostic.
            return new Readback.NotReady.Unreadable<>(module,
                    new Readback.Failure.UnresolvedPublishedNames());
        }
        return new Readback.Ready<>(new Read(resolution.module(),
                readable.behaviorImplementations()));
    }
}
