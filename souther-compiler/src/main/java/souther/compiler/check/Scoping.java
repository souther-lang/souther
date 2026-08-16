package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeSymbols;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What the names a module writes can mean, worked out against a {@link ModuleUniverse}.
 *
 * <p>The one place a module's name-resolution environment is derived. A universe supplies facts
 * about modules — what it has under a name — and everything after that is here: what a bare type
 * name denotes, which module a qualifier stands for, what a bare name in the value namespace
 * reaches, and what an import line could not do.
 *
 * <p>Written this way because the same rules were being applied twice, once by a compilation
 * reading its own sources and once by a reader putting published classes back together, and each
 * was right on its own. What that cost was a module that compiled in the project that wrote it and
 * refused to be imported anywhere else: the two readings disagreed about what one import line
 * brought in, and nothing was written down that said they had to agree. So which universe answered
 * is the only thing that differs between the two; what is done with the answers is this.
 *
 * <p>Nothing here reports. An import line that names a module nothing has is a {@link Refusal}, and
 * what to do about one is the caller's: a compilation says it to the author, and a reader that is
 * only reading takes it as this module not being readable here. A walk that made diagnostics could
 * not be used by the second reader without saying things to nobody.
 */
public final class Scoping {

    private Scoping() {}

    /**
     * What a module is resolved against, in {@code universe}.
     *
     * <p>Only a module the universe can read has a scope. One it has and cannot read has no
     * declarations to give, and a scope assembled around the hole would say what a name means in a
     * module nothing can say anything about.
     */
    public static Scoped of(ModuleUniverse universe, Subject subject) {
        Ast.Module m = subject.module();
        List<Refusal> refused = new ArrayList<>();
        Map<String, Denotation> denotations = new LinkedHashMap<>();
        Map<String, String> aliases = new LinkedHashMap<>();
        for (Ast.Def own : subject.declared().declarations().values()) {
            denotations.put(own.name(),
                    new Denotation.Denotes(TypeSymbols.declared(own.declaredKey())));
        }
        // Which import brought each name in, so a second one naming it is reported against that
        // import rather than against a local definition the module may not have.
        Map<String, Ast.Import> from = new HashMap<>();
        // An import line that is wrong is refused and skipped, and the ones that are fine still
        // bring in what they bring in. A half-typed import is as ordinary as a half-typed name, and
        // taking the whole scope away would leave every name in the file meaning nothing — which is
        // when an author most wants to be told what one means.
        for (Ast.Import imp : importsOf(universe, m)) {
            ModuleUniverse.InSight.Read there;
            switch (universe.module(imp.module())) {
                case ModuleUniverse.InSight.Read read0 -> there = read0;
                // Being part of this universe and being part of it while saying nothing usable are
                // different things, and only the second is the importer's business. Whatever is
                // wrong with a module that is here is answered where it is; saying it again here
                // sends the author to a file that is fine.
                case ModuleUniverse.InSight.Unreadable _ -> there = null;
                case ModuleUniverse.InSight.Unknown _ -> {
                    refused.add(new Refusal.NoSuchModule(imp));
                    there = null;
                }
            }
            if (there == null) {
                nameless(denotations, imp.names());
                continue;
            }
            if (imp.alias() != null) {
                String taken = aliasTakenBy(universe, imp.alias(), aliases);
                if (taken != null) {
                    refused.add(new Refusal.AliasTaken(imp, taken));
                    nameless(denotations, imp.names());
                    continue;   // an alias that names two things names neither here
                }
                aliases.put(imp.alias(), imp.module());
            }
            for (String imported : imp.names()) {
                if (!there.exposes(imported)) {
                    refused.add(new Refusal.NotExposed(imp, imported));
                    nameless(denotations, List.of(imported));
                    continue;
                }
                Ast.Def brought = there.declaration(imported);
                if (brought == null) {
                    // a behavior import is resolved separately, and so is a value or a helper: none
                    // of them is a data Def, so none goes into the type namespace
                    if (there.declaresBehavior(imported) || there.declaresValue(imported)) {
                        continue;
                    }
                    refused.add(new Refusal.NoSuchName(imp, imported));
                    nameless(denotations, List.of(imported));
                    continue;
                }
                if (denotations.get(imported) instanceof Denotation.Denotes) {
                    // Which of the two is asked of what has the name, not of what this module
                    // declares: an import that brought it in is in `from`, and one that did not is
                    // an import against a declaration. Read the other way round, the second could
                    // be told to name an import that is not there.
                    Ast.Import earlier = from.get(imported);
                    refused.add(earlier == null
                            ? new Refusal.CollidesWithADeclaration(imp, imported)
                            : new Refusal.BroughtTwice(imp, imported, earlier));
                    continue;   // the first claim on the name keeps it
                }
                // A name a failed import line only stood in for is not a claim on it: an import
                // that can do the job takes it, and says nothing about the line that could not.
                // Which declaration it is is the declaration's to say: an identity made here from
                // the import line's module and the spelling would answer for a declaration
                // whatever the name came from.
                denotations.put(imported,
                        new Denotation.Denotes(TypeSymbols.declared(brought.declaredKey())));
                from.put(imported, imp);
            }
        }
        Resolve.Values values =
                new Resolve.Values(reachable(universe, subject), new OfTheUniverse(universe));
        refused.addAll(oneSpellingTwice(universe, subject));
        return new Scoped(m.name(), denotations, aliases, values, refused);
    }

    /**
     * The module a scope is being assembled for, and what only it needs.
     *
     * <p>The module itself is here and not in the universe. A module being scoped is the one this
     * reads the syntax of — its import lines, its bodies, the names its declarations write — and
     * that is a capability nothing has over any other module: what a universe answers about a
     * neighbour is what was settled about it ({@link ModuleUniverse.InSight.Read}), asked one name
     * at a time, so no walk can work the same facts out a second way. Its own declaration index is
     * here for the same reason and from the other side — reading every one of them is what a
     * module may do to itself and to nothing else.
     *
     * <p>One value, because the parts cannot be told apart afterwards. The
     * {@code import List ( map )} lines are dropped once read ({@link Exposing}), so what they
     * brought in outlives them and travels with the module or is lost — read as a second answer it
     * was answered emptily for a module off the class path, and every bare name in a published
     * invariant then denoted nothing.
     *
     * <p>Told apart from what the universe says about the modules around it, because it is a fact
     * about here and not about them. A reader of another module never asks what that module may
     * write bare, and a universe that answered it anyway would put every importer's scope behind an
     * edit to a library import line in a module it imports from.
     */
    public record Subject(Ast.Module module, Registry.Declared<Ast.Def> declared,
                          Map<String, ValueName.Stdlib> libraryNames) {

        public Subject {
            libraryNames = Collections.unmodifiableMap(new LinkedHashMap<>(libraryNames));
        }
    }

    /**
     * What a module is resolved against: what each name it writes can mean, and what an import line
     * could not do.
     *
     * <p>One value for both namespaces, because a name written in a module means one thing and the
     * question of what that is was being asked twice — once of the type namespace and once of the
     * value namespace — with the import lines walked once for each. A spelling that arrives in both
     * is a clash, and a walk that only ever saw one of them could not say so.
     *
     * <p>The table and the way of asking the universe a further question are here as one pair
     * rather than the table alone. The universe is not a free axis — it is what this was assembled
     * against — so a caller that had to put the two together could put a table with a second
     * universe, leaving what an import brought in decided by one and what a qualifier names by the
     * other. The declaration registry is handed over at the point of use for the opposite reason:
     * one compilation genuinely reads one scope against three stages of its declarations.
     */
    public record Scoped(String module, Map<String, Denotation> denotations,
                         Map<String, String> aliases, Resolve.Values values,
                         List<Refusal> refused) {

        /** Copied, for the reason {@link Exposing.Checked} is: this is an answer a compilation
         *  remembers, and an answer it remembers is a value. */
        public Scoped {
            denotations = Collections.unmodifiableMap(new LinkedHashMap<>(denotations));
            aliases = Collections.unmodifiableMap(new LinkedHashMap<>(aliases));
            refused = List.copyOf(refused);
        }

        /**
         * What {@code Resolve} reads this module against, over the declarations as they were
         * written.
         *
         * <p>Made here and not by a caller holding the parts. The scope, the aliases and the module
         * name come out of one assembly and mean nothing apart from each other; passed separately
         * they could be paired with parts of another, and nothing in what a caller was holding
         * would have said so. The registry is the one thing left to hand over, because it really is
         * a free axis: one compilation reads the same scope against its written, its resolved and
         * its derived declarations.
         */
        public SyntaxSymbols writtenSymbols(Registry<Ast.Def> registry) {
            return SyntaxSymbols.of(module, registry, denotations, aliases);
        }

        /** What this module can name in the value namespace, on its own. What a reader wanting to
         *  know what may be written here asks for; the pair is what the resolve pass is given. */
        public Resolve.Reachable reachable() {
            return values.reachable();
        }

        /** The same over a stage of the declarations something has resolved. */
        public Symbols symbolsOver(Registry<Hir.Def> registry) {
            return Symbols.of(module, registry, denotations, aliases);
        }
    }

    /**
     * A reason the scope a module asked for cannot hold a name.
     *
     * <p>Each of these carries what it is about rather than what to say about it. A compilation
     * turns them into diagnostics where it reads the result; a reader that is only reading a module
     * takes one as the module not being readable here. Values because the second reader has to tell
     * them apart, and a diagnostic can only be counted.
     */
    public sealed interface Refusal {

        /** The import names a module this universe does not have. */
        record NoSuchModule(Ast.Import imp) implements Refusal {}

        /** The module is there and does not expose the name. */
        record NotExposed(Ast.Import imp, String name) implements Refusal {}

        /** The module is there and declares nothing of that name. */
        record NoSuchName(Ast.Import imp, String name) implements Refusal {}

        /** The alias is a qualifier something already answers to — another alias, a module of this
         *  universe, or the standard library. */
        record AliasTaken(Ast.Import imp, String takenBy) implements Refusal {}

        /** Two imports bring the same bare name in. {@code earlier} is the one that has it, and
         *  there is always one: an import against a declaration is the arm below. */
        record BroughtTwice(Ast.Import imp, String name, Ast.Import earlier) implements Refusal {

            public BroughtTwice {
                java.util.Objects.requireNonNull(earlier, "the import that already brought it in");
            }
        }

        /** An import brings in a name this module declares itself. */
        record CollidesWithADeclaration(Ast.Import imp, String name) implements Refusal {}

        /** A declaration takes a standard-library qualifier, which is no module's to shadow. */
        record TakesTheLibraryQualifier(Ast.Def def) implements Refusal {}

        /** A {@code let} and a data are written under one spelling. */
        record ALetAndADataShareASpelling(Ast.FnDef fn) implements Refusal {}
    }

    /**
     * Puts {@code names} in scope as names that denote nothing.
     *
     * <p>An import line that could not do its job was refused on that line. A name it was to bring
     * in is in scope all the same, denoting nothing — so a use of it takes the error type and says
     * nothing more. Leaving it out of scope instead would report an unknown type at every use, which
     * sends the author to a field when what is wrong is the import.
     */
    private static void nameless(Map<String, Denotation> denotations, List<String> names) {
        for (String written : names) {
            denotations.putIfAbsent(written, Denotation.STANDS_FOR_NOTHING);
        }
    }

    /**
     * What already answers to {@code alias} as a qualifier, or null where nothing does.
     *
     * <p>An alias must be a qualifier nothing else already is: another alias, a module of this
     * universe, or a standard-library qualifier. Left to win silently it would take over what
     * {@code List.map} or {@code billing.Amount} means here.
     */
    private static String aliasTakenBy(ModuleUniverse universe, String alias,
                                       Map<String, String> aliases) {
        if (aliases.containsKey(alias)) {
            return aliases.get(alias);
        }
        if (universe.module(alias).isThere()) {
            return alias;
        }
        return Prelude.isQualifier(alias) ? "souther" : null;
    }

    /**
     * What a module's bodies can name without a binding: its own helpers, the definitions its
     * imports bring in, and every behavior it can reach.
     *
     * <p>Whether the behaviors are all of them is worked out here rather than decided by whoever
     * built the universe. An import naming a module that cannot be read may have been where a bare
     * name came from, and a reader that answered "all of them" for a universe it had not finished
     * reading would report the name as denoting nothing.
     */
    private static Resolve.Reachable reachable(ModuleUniverse universe, Subject subject) {
        Ast.Module m = subject.module();
        // A behavior's `let` is not a helper: it implements the behavior, and the name reaches the
        // behavior. Asked the same way as HelperInliner.helpersOf, which decides what is expanded —
        // two answers to one question is how a name came to denote a helper here and a behavior
        // there.
        Set<String> behaviorNames = behaviorNames(m);
        Map<String, ValueName.Helper> helpers = new LinkedHashMap<>();
        for (Ast.FnDef fn : m.fns()) {
            if (HelperInliner.isHelperName(behaviorNames, fn.name())) {
                helpers.put(fn.name(), new ValueName.Helper(m.name(), fn.name()));
            }
        }
        Map<String, ValueName.Behavior> behaviors = new LinkedHashMap<>();
        for (String own : behaviorNames) {
            behaviors.put(own, new ValueName.Behavior(m.name(), own));
        }
        boolean whole = true;
        // A definition another module publishes is written here bare, like one of this module's own
        // — a value substituted at its reference, a helper expanded at its call (ADR-0072). What it
        // denotes is the module that declares it: the bare spelling is this module's way of writing
        // it, and the pair (module, name) is what the definition is. A reader that spells one of
        // its own the same way is a name clash, which the import check refuses.
        for (Ast.Import imp : m.imports()) {
            if (!(universe.module(imp.module()) instanceof ModuleUniverse.InSight.Read there)) {
                whole = false;
                continue;
            }
            for (String imported : imp.names()) {
                if (there.publishedHelper(imported).isPresent()) {
                    helpers.putIfAbsent(imported,
                            new ValueName.Helper(imp.module(), imported));
                }
                if (there.declaresBehavior(imported)) {
                    // a name this module declares itself is the one it means
                    behaviors.putIfAbsent(imported,
                            new ValueName.Behavior(imp.module(), imported));
                }
            }
        }
        return new Resolve.Reachable(m.name(), helpers, behaviors, whole, subject.libraryNames());
    }

    /**
     * What resolution can be told about the behaviors of the modules around this one.
     *
     * <p>Asked by name while a module is being resolved, and left that way. Which modules a
     * qualified behavior reference names is settled by resolution — a qualifier is whatever the
     * author wrote — so a set worked out here would be this walk guessing what that one will ask,
     * and a guess that came up short would answer "no module of that name" for a module that is
     * there. Nothing derived is held: this is the universe, asked the questions it exists to
     * answer.
     *
     * <p>A record, and not the closure it reads like, because it is a value: two of these put the
     * same question to the same universe and are the same thing. What it is part of is remembered,
     * and an answer a compilation keeps is compared with the next one to decide whether the work
     * that read it has to be done again — so an object that never equals the last one is an answer
     * that is never kept.
     */
    record OfTheUniverse(ModuleUniverse universe) implements Resolve.Elsewhere {

        @Override
        public boolean hasModule(String name) {
            return universe.module(name).isThere();
        }

        @Override
        public Resolve.Declares declaresBehavior(String module, String name) {
            if (!(universe.module(module) instanceof ModuleUniverse.InSight.Read read)) {
                return Resolve.Declares.CANNOT_SAY;
            }
            return read.declaresBehavior(name) ? Resolve.Declares.YES : Resolve.Declares.NO;
        }

        @Override
        public Set<String> behaviorNamesToSuggest(String module) {
            return universe.module(module) instanceof ModuleUniverse.InSight.Read read
                    ? read.behaviorNamesToSuggest() : Set.of();
        }
    }

    /**
     * Every spelling that reaches this module's value namespace twice.
     *
     * <p>A data reaches it — a unit data is a value, a newtype is applied to what it wraps, a record
     * is constructed by its name — and so do a {@code let}, a behavior, a definition another module
     * publishes, and a standard-library qualifier. One name means one thing there, whichever way it
     * arrived. A spelling with two meanings is answered by whichever reader looks first, which is
     * how a name could be a unit data where it stood alone and an imported helper where it was
     * applied.
     *
     * <p>Asked here because this is where the namespace is assembled. A rule stated per arrival
     * would have to be restated for each new way in.
     *
     * <p>A behavior and a {@code let} of one name are not two: they are the declaration and the
     * implementation of one thing (ADR-0072).
     */
    private static List<Refusal> oneSpellingTwice(ModuleUniverse universe, Subject subject) {
        Ast.Module m = subject.module();
        List<Refusal> refused = new ArrayList<>();
        // What the module has, as it was settled — not what its text writes. A declaration it does
        // not have is refused where declarations are indexed, and a second reading of the text here
        // would be a second answer to which of them it has.
        Map<String, Ast.Def> declared = subject.declared().declarations();
        for (Ast.Def def : declared.values()) {
            // A standard-library qualifier is the only spelling that reaches the library, so a data
            // of that name hides it — from every module, since the qualifier is not this module's
            // to shadow. Refused where it is declared, as a reserved module name is.
            if (Prelude.isQualifier(def.name())) {
                refused.add(new Refusal.TakesTheLibraryQualifier(def));
            }
        }
        Set<String> implementing = behaviorNames(m);
        for (Ast.FnDef fn : m.fns()) {
            if (!implementing.contains(fn.name()) && declared.containsKey(fn.name())) {
                refused.add(new Refusal.ALetAndADataShareASpelling(fn));
            }
        }
        // What this module declares under a name, whichever kind of declaration it is: a data, a
        // `let`, a behavior. A behavior and its `let` are one of them, so the set is what is asked
        // rather than a count.
        Set<String> ownNames = new LinkedHashSet<>(declared.keySet());
        ownNames.addAll(implementing);
        for (Ast.FnDef fn : m.fns()) {
            ownNames.add(fn.name());
        }
        // A name an import brings in is written here bare (ADR-0075), so it arrives in this
        // namespace exactly as one of this module's own does — and collides the same way. Which
        // kind of thing each side is does not enter into it: the reader writes one spelling, and
        // one spelling here means one thing.
        for (Ast.Import imp : m.imports()) {
            for (String imported : intoTheValueNamespace(universe, imp)) {
                if (ownNames.contains(imported)) {
                    refused.add(new Refusal.CollidesWithADeclaration(imp, imported));
                }
            }
        }
        return refused;
    }

    /**
     * The names {@code imp} brings into the value namespace: the definitions the module publishes,
     * the behaviors it declares and the types it declares, all of which a reader writes bare. A type
     * is one of them because a unit data is a value, a newtype is applied to what it wraps and a
     * record is constructed by its name — the type namespace refuses a type against a type, so what
     * a type adds here is a type against a {@code let} or a behavior.
     *
     * <p>Only what the module exposes, and only what the line asks for. A name the line names and
     * the module does not expose is nothing this import brought in, and refusing it here would tell
     * the author to rename a definition that is not what is wrong — the line is answered by
     * {@link Refusal.NotExposed}, which is the whole of it.
     *
     * <p>A library import is not here. Those lines are read where the table they fill is built
     * ({@link Exposing}) and are gone from the module by the time this is asked.
     */
    private static Set<String> intoTheValueNamespace(ModuleUniverse universe, Ast.Import imp) {
        if (!(universe.module(imp.module()) instanceof ModuleUniverse.InSight.Read there)) {
            return Set.of();
        }
        Set<String> names = new LinkedHashSet<>();
        for (String name : imp.names()) {
            if (there.publishedHelper(name).isPresent()) {
                names.add(name);
                continue;
            }
            if (!there.exposes(name)) {
                continue;
            }
            if (there.declaresBehavior(name) || there.declaration(name) != null) {
                names.add(name);
            }
        }
        return names;
    }

    /**
     * The imports a module has: the ones it wrote, and the ones a qualified reference in its header
     * asked for.
     *
     * <p>Naming a behavior through its module reaches into that module whether or not an import
     * line says so: the borrowed signature and the injected field are found by an import, and the
     * module is a dependency for the same reason. So it is answered here, off the spellings the
     * header writes.
     *
     * <p>Whether the behavior is there at all is not asked beyond the module declaring it. A name
     * that module does not declare is borrowed from nowhere, and that it names nothing is answered
     * where the clause is read.
     */
    public static List<Ast.Import> importsOf(ModuleUniverse universe, Ast.Module m) {
        List<Ast.Import> imports = new ArrayList<>(m.imports());
        Map<String, Set<String>> borrowed = borrowed(universe, m);
        for (Map.Entry<String, Set<String>> reached : borrowed.entrySet()) {
            Set<String> already = new LinkedHashSet<>();
            for (Ast.Import imp : m.imports()) {
                if (imp.module().equals(reached.getKey())) {
                    already.addAll(imp.names());
                }
            }
            List<Ast.ImportedName> names = new ArrayList<>();
            for (String bare : reached.getValue()) {
                if (!already.contains(bare)) {
                    // No position on a synthesized name: nobody wrote it on an import list. The
                    // qualified reference that asked for it is where it came from.
                    names.add(new Ast.ImportedName(bare, null));
                }
            }
            if (!names.isEmpty()) {
                imports.add(new Ast.Import(reached.getKey(), null, names, m.pos()));
            }
        }
        return imports;
    }

    /** The behaviors this module names through another module's name, by that module. */
    public static Map<String, Set<String>> borrowed(ModuleUniverse universe, Ast.Module m) {
        Map<String, String> qualifiers = aliases(m);
        Map<String, Set<String>> out = new LinkedHashMap<>();
        for (Ast.Var ref : qualifiedBehaviorRefs(m)) {
            String written = ref.name();
            String target = moduleNamedBy(written, qualifiers);
            if (target == null || target.equals(m.name())
                    || !(universe.module(target) instanceof ModuleUniverse.InSight.Read read)) {
                continue;
            }
            String bare = written.substring(written.lastIndexOf('.') + 1);
            if (read.declaresBehavior(bare)) {
                out.computeIfAbsent(target, k -> new LinkedHashSet<>()).add(bare);
            }
        }
        return out;
    }

    /** Each {@code import ... as} alias, against the module it stands for. */
    public static Map<String, String> aliases(Ast.Module m) {
        Map<String, String> qualifiers = new HashMap<>();
        for (Ast.Import imp : m.imports()) {
            if (imp.alias() != null) {
                qualifiers.put(imp.alias(), imp.module());
            }
        }
        return qualifiers;
    }

    /** The module a qualified spelling names, by its qualifier — an alias, or a module named under
     * its own name. Null where the spelling carries no qualifier. */
    public static String moduleNamedBy(String written, Map<String, String> qualifiers) {
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            return null;
        }
        String qualifier = written.substring(0, dot);
        return qualifiers.getOrDefault(qualifier, qualifier);
    }

    /** Every name the behavior namespace writes with a qualifier: a {@code >->} stage, a
     *  {@code depends on}. */
    public static List<Ast.Var> qualifiedBehaviorRefs(Ast.Module m) {
        List<Ast.Var> out = new ArrayList<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            List<Ast.Var> refs = switch (b) {
                case Ast.PipeBehavior pipe -> pipe.stages();
                case Ast.SpecBehavior spec -> spec.dependsOn();
            };
            for (Ast.Var ref : refs) {
                if (ref.name().lastIndexOf('.') >= 0 && !Resolve.namesABoundaryEdge(ref.name())) {
                    out.add(ref);
                }
            }
        }
        return out;
    }

    /** The behavior names a module declares. */
    public static Set<String> behaviorNames(Ast.Module m) {
        Set<String> names = new LinkedHashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            names.add(b.name());
        }
        return names;
    }
}
