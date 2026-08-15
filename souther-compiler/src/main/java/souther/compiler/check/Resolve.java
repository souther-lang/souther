package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.ReachName;
import souther.compiler.types.Type;
import souther.compiler.types.Denotation;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;
import souther.compiler.Reserved;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Says once, for a whole module, what every written type name denotes.
 *
 * <p>Before this pass a name is a spelling: {@code 金額}, {@code billing.金額}, or an alias'd
 * {@code B.金額}, and whether the three mean one type is a question each consumer used to answer for
 * itself — which is why a capability reached the positions someone wired it to and no others
 * (issues #101, #113, #124, #132, #154). After it, every {@link Ast.Name} in the tree carries the
 * {@link TypeSymbol} it denotes, and a check that wants to know whether two names are the same type
 * compares what they denote. There is no spelling left to compare.
 *
 * <p>A name that denotes nothing is reported here and is {@link Hir.Name.Unanswered} from there on
 * — a state of the name and not a stand-in identity, so nothing below reads it as a declaration and
 * nothing below has a spelling to fall back to. Where a type reference stands on such a name, what
 * it denotes is {@link souther.compiler.types.Type#ERRONEOUS}. The pass does not stop: the rest of
 * the module is resolved
 * as if the mistake were not there, which is what lets an author be told about every unknown name at
 * once and lets an editor still say what the names around one mean. A name a pass synthesized
 * already knowing what it means (a codec {@code Deriver} builds from a field's type) is left as it
 * is.
 */
public final class Resolve {

    private final SyntaxSymbols symbols;
    private final Values values;
    /** Every name this pass answered, in the order it met them. */
    private final List<TypeUse> denotations = new ArrayList<>();
    /** The same, for the names used as values. */
    private final List<ValueUse> values0 = new ArrayList<>();
    /** What it has to say about the names it could not answer, as the errors it would once have
     * thrown. Not every one of them is in here: some are already reported elsewhere. */
    private final List<CompileException> unresolved = new ArrayList<>();
    /**
     * How many names it could not answer, by every route there is.
     *
     * <p>Counted apart from what was said about them, because they are two things. A name is left
     * unanswered and said nothing about where the reason is somewhere else and already reported
     * there — a module this compilation has and cannot use has its exported names put in an
     * importer's scope as identities nothing declares, so the importer is not told a second time
     * about a file that is fine. That is the same absence as a misspelling; only the report differs.
     * Whether a declaration's names came out is this, and never how many diagnostics were added
     * while it was being read.
     */
    private int failed;
    /** What each binding this pass gave an identity to is called, and where that is written. */
    private final Map<BindingId, BoundName> binders = new LinkedHashMap<>();
    /** How many bindings each definition has been given, so the next one gets the next number. */
    private final Map<BindingOwner, Integer> counts = new HashMap<>();
    /** The definition whose text is being read. Every binding met belongs to it. */
    private BindingOwner owner;

    /**
     * Whether what is being resolved was written in an {@code example} or {@code fake} row.
     *
     * <p>The one thing this decides is which node a bracketed literal becomes: in a row the brackets
     * are the notation for whichever collection the position declares, and which one that is has no
     * answer until the position is known, so the node says so rather than being read as a list here
     * (spec §example-evaluable). Nothing else about a row is resolved differently, and nothing here
     * reads a type.
     */
    private boolean inARow;
    /**
     * The behaviors this module named through another module's name, by that module.
     *
     * <p>A qualified stage reaches a behavior whether or not an import says so, and the borrowed
     * signature and the injected field are found by an import. So naming one asks for the import,
     * and the import is written here rather than left for a reader to work out from the spelling.
     */
    private final Map<String, Set<String>> borrowed = new LinkedHashMap<>();
    /** Where each of those was first named — the position the synthesized import stands at. */
    private final Map<String, SourcePos> borrowedAt = new LinkedHashMap<>();

    private Resolve(SyntaxSymbols symbols, Values values) {
        this.symbols = symbols;
        this.values = values;
    }

    /** The value definition of this spelling in this module. */
    private BindingOwner ownerOfValue(String name) {
        return new BindingOwner.OfValue(values.module(), name);
    }

    /** A binder answered, and the bindings that hold under it. */
    private record Answered(Hir.Binder binder, Bindings bound) {}

    /**
     * {@code binder} given a binding of its own, and {@code bound} extended with it.
     *
     * <p>The binding is what the names under it are answered with, so two bindings of one spelling
     * are two answers however they were written. Where it was written is kept aside, for a reader
     * that is asking about the source rather than about the program.
     */
    private Answered bind(Bindings bound, Ast.Binder binder) {
        int ordinal = counts.merge(owner, 1, Integer::sum) - 1;
        BindingId id = new BindingId(owner, ordinal);
        if (binder.namePos() != null) {
            // Only a name the author wrote is a place a reader can be sent to or asked about. A
            // desugaring's binding is anchored on the form it came from, which is a place holding
            // something the author did write.
            binders.put(id, new BoundName(binder.written()));
        }
        return new Answered(
                new Hir.Binder(binder.written(), id, binder.pos()),
                bound.and(binder.name(), new ValueName.Local(binder.name(), id)));
    }

    /** Several binders answered, and the bindings that hold under all of them. */
    private record AnsweredAll(List<Hir.Binder> binders, Bindings bound) {}

    /** The same as {@link #bind}, for the names one binder writes at once — a block's parameters. */
    private AnsweredAll bindAll(Bindings bound, List<Ast.Binder> written) {
        List<Hir.Binder> out = new ArrayList<>();
        for (Ast.Binder b : written) {
            Answered a = bind(bound, b);
            bound = a.bound();
            out.add(a.binder());
        }
        return new AnsweredAll(out, bound);
    }

    /**
     * What a module can name in the value namespace without a binding: its own helpers, and the
     * behaviors it can reach.
     *
     * <p>The behaviors come from outside — an import brings one in — so they are given rather than
     * read off the module. A module resolved on its own reaches only what it declares.
     */
    public record Values(String module, Map<String, ValueName.Helper> helpers,
                         Map<String, ValueName.Behavior> behaviors, boolean behaviorsWhole,
                         Map<String, ValueName.Stdlib> exposed, Elsewhere elsewhere) {

        /**
         * What a module reaches when nothing else is in sight — the core modules, which the library
         * resolves as it loads. A core module imports nothing (it declares the library), so the
         * table of names an import would bring in is empty; a module that does import is resolved
         * with what the query answered, which reads its imports from the source that wrote them.
         */
        public static Values of(Ast.Module m) {
            Map<String, ValueName.Behavior> behaviors = new LinkedHashMap<>();
            for (Ast.BehaviorDef b : m.behaviors()) {
                behaviors.put(b.name(), new ValueName.Behavior(m.name(), b.name()));
            }
            Map<String, ValueName.Helper> helpers = new LinkedHashMap<>();
            for (Ast.FnDef fn : m.fns()) {
                if (HelperInliner.isHelperName(behaviors.keySet(), fn.name())) {
                    helpers.put(fn.name(), new ValueName.Helper(m.name(), fn.name()));
                }
            }
            return new Values(m.name(), helpers, behaviors, true, Map.of(), Elsewhere.NONE);
        }
    }

    /**
     * What this module can be told about the behaviors of the modules around it, asked one question
     * at a time.
     *
     * <p>A stage may name a behavior of a module this one has not imported, which is what says the
     * import has to be synthesized; answering that needs the other module, and it is asked for by
     * name rather than handed over so that a compilation reaching no other module reads none.
     */
    public interface Elsewhere {

        /** Nothing else in sight — a module resolved on its own. */
        Elsewhere NONE = new Elsewhere() {
            @Override
            public boolean hasModule(String name) {
                return false;
            }

            @Override
            public Set<String> behaviorsOf(String module) {
                return Set.of();
            }
        };

        /** Whether this compilation has a module of that name. */
        boolean hasModule(String name);

        /**
         * The behaviors that module declares, or null where this compilation has it and cannot read
         * it — which is not the same as its declaring none. Whatever is wrong with it is reported on
         * its own source, so a name that may have come from there is left unanswered and said
         * nothing about.
         */
        Set<String> behaviorsOf(String module);
    }

    /**
     * One written name and what it turned out to denote, where it was written.
     *
     * <p>This is the pass's other product. Working out what a name means is a traversal of the whole
     * module, and an editor asking "what is under the cursor" or "where else is this named" is asking
     * about the answers that traversal already gave. Collecting them here is what keeps the editor
     * from walking the tree again with a rule of its own — which, before this, is how renaming a
     * type could rewrite the tail of a qualified reference to a different module's type.
     *
     * @param written the occurrence the name was read from — the name, the characters that spell
     *                it there, and where they are
     * @param denotes what it names
     */
    public record TypeUse(WrittenName written, TypeSymbol denotes) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * One written name in the value namespace and what it turned out to denote, where it was
     * written. What {@link TypeUse} is for a type, and collected for the same reason: an editor
     * asking what is under the cursor is asking about the answer this traversal already gave.
     */
    public record ValueUse(WrittenName written, ValueName denotes) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /**
     * What the pass worked out about the names a module writes, and nothing else.
     *
     * <p>Every entry is an answer it reached. A name it could not answer is in none of them, so a
     * reader asking about one is told there is nothing there rather than handed a declaration that
     * was never written — the identity the traversal carries past a mistake stands for the absence
     * and is not an identity anything declares. This is what a reader outside the compiler is
     * offered, which is why it is a partial record rather than a total one: an incomplete module has
     * incomplete answers about it, and the answers it does have are as good as any other module's.
     *
     * <p>{@code binders} says what each binding is called and where the author wrote that name. A
     * binding is not its position — a pass that expands a helper stamps the call site over the
     * positions in the copy — so the two are kept apart, and a reader asking about the source rather
     * than about the program reads this. The characters that spell it come with it, because a reader
     * asking what a cursor is on has to know how far the name reaches, and neither a position nor
     * the name alone says.
     *
     * <p>Only the bindings whose names the author wrote are in it. A desugaring binds a value to a
     * name of its own — the parameter {@code .field} becomes, the value a {@code match} is held in —
     * and anchors it on the form it was rewriting. That anchor is a place in the source holding
     * something else, so a reader answered with one of these would be answered about a name that is
     * not there, at a width that is not its.
     */
    public record ResolutionIndex(List<TypeUse> types, List<ValueUse> values,
                                  Map<BindingId, BoundName> binders) {}

    /**
     * A resolved module, what the pass worked out about the names in it, and the names it could not
     * answer.
     *
     * <p>A name that denotes nothing does not end the pass. It is {@link Hir.Name.Unanswered}, a
     * type reference standing on one denotes {@link souther.compiler.types.Type#ERRONEOUS}, and the
     * rest of the module is resolved as if the mistake were not there — so an author is told about
     * every unknown name at once instead of one per compile, and an editor can still say what the
     * names around it mean.
     */
    public record Resolution(Hir.Module module, ResolutionIndex index,
                             List<CompileException> unresolved,
                             Map<String, OfDeclaration> declarations) {}

    /**
     * What resolving one declaration came to.
     *
     * <p>{@code answered} is whether every name written in it was answered — the names met while it
     * was being read, and no others, so a mistake in the declaration beside it is not one of these.
     * {@code reaches} is what those names turned out to denote, which is what says whether this
     * declaration stands on one that has no meaning.
     */
    public record OfDeclaration(boolean answered, Set<TypeSymbol> reaches) {}

    /** What a binding is called, and the occurrence of that name the author wrote. */
    public record BoundName(WrittenName written) {

        /** Where the name is written. */
        public SourcePos pos() {
            return written.pos();
        }
    }

    /** {@code m} with every name it writes resolved against its own definitions — a module compiled
     * with nothing else in sight. */
    public static Hir.Module module(Ast.Module m) {
        return module(m, SyntaxSymbols.of(m));
    }

    /** {@code m} with every name it writes resolved against {@code symbols}. */
    public static Hir.Module module(Ast.Module m, SyntaxSymbols symbols) {
        Resolution resolved = resolving(m, symbols);
        if (!resolved.unresolved().isEmpty()) {
            // This entry point answers with a module or not at all, which is what its one caller —
            // loading the shipped core — needs: a misspelled type in a prelude resource is a fault in
            // the compiler, not something an author can be told about and carry on past.
            throw resolved.unresolved().get(0);
        }
        return resolved.module();
    }

    /** As {@link #module(Ast.Module, SyntaxSymbols)}, keeping what each name was answered with. */
    public static Resolution resolving(Ast.Module m, SyntaxSymbols symbols) {
        return resolving(m, symbols, Values.of(m));
    }

    /** As {@link #resolving(Ast.Module, SyntaxSymbols)}, with what the module reaches in the value
     * namespace given rather than read off the module itself. */
    public static Resolution resolving(Ast.Module m, SyntaxSymbols symbols, Values values) {
        Resolve r = new Resolve(symbols, values);
        List<Hir.Def> defs = new ArrayList<>();
        // Which names were answered is settled per declaration: what one of them writes is nothing
        // the one beside it wrote, and the names met while it was being read are its own.
        Map<String, OfDeclaration> declarations = new LinkedHashMap<>();
        // What the module declares, rather than what its text writes. A second declaration of a name
        // and a built-in case name are refused where declarations are indexed, and this pass is not
        // where that is decided again: reading them here would mean answering for a declaration
        // nothing else in the compilation has, which can only be done by making up an identity for
        // it.
        for (Map.Entry<TypeSymbol, Ast.Def> declared : symbols.declaredHere().entrySet()) {
            int failedBefore = r.failed;
            int denotedBefore = r.denotations.size();
            Hir.Def resolved = r.def(declared.getKey(), declared.getValue());
            defs.add(resolved);
            Set<TypeSymbol> reaches = new LinkedHashSet<>();
            for (TypeUse d : r.denotations.subList(denotedBefore, r.denotations.size())) {
                reaches.add(d.denotes());
            }
            declarations.put(resolved.name(),
                    new OfDeclaration(r.failed == failedBefore, Set.copyOf(reaches)));
        }
        List<Hir.BehaviorDef> behaviors = new ArrayList<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            behaviors.add(switch (b) {
                case Ast.SpecBehavior spec -> new Hir.SpecBehavior(spec.written(), r.params(spec.params()),
                        r.retType(spec.ret()), r.names(spec.constructs()),
                        r.required(spec.dependsOn(), spec.name()), spec.pos());
                case Ast.PipeBehavior pipe -> new Hir.PipeBehavior(pipe.written(),
                        r.stages(pipe.stages()), r.retType(pipe.declaredOut()), pipe.pos());
            });
        }
        List<Hir.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(r.fn(fn));
        }
        List<Hir.Example> examples = new ArrayList<>();
        r.inARow = true;   // every operand below is written in a row (spec §example-evaluable)
        for (Ast.Example e : m.examples()) {
            r.owner = r.ownerOfValue(e.target());
            List<Hir.ExampleRow> rows = new ArrayList<>();
            for (Ast.ExampleRow row : e.rows()) {
                List<Hir.With> withs = new ArrayList<>();
                for (Ast.With w : row.withs()) {
                    withs.add(new Hir.With(w.dep(), r.expr(w.value()), w.pos()));
                }
                rows.add(new Hir.ExampleRow(row.identity(), r.exprs(row.inputs()), withs,
                        r.expr(row.expected()), row.pos()));
            }
            examples.add(new Hir.Example(e.target(), rows, e.pos()));
        }
        List<Hir.Fake> fakes = new ArrayList<>();
        for (Ast.Fake f : m.fakes()) {
            r.owner = r.ownerOfValue(f.target());
            List<Hir.FakeRow> rows = new ArrayList<>();
            for (Ast.FakeRow row : f.rows()) {
                rows.add(new Hir.FakeRow(row.inputs() == null ? null : r.exprs(row.inputs()),
                        r.expr(row.output()), row.isDefault(), row.pos()));
            }
            fakes.add(new Hir.Fake(f.target(), rows, f.pos()));
        }
        r.inARow = false;
        Map<String, Hir.RetType> exposedOutputs = new LinkedHashMap<>();
        for (Map.Entry<String, Ast.RetType> e : m.exposedOutputs().entrySet()) {
            exposedOutputs.put(e.getKey(), r.retType(e.getValue()));
        }
        if (!m.takenOn().isEmpty()) {
            // What a module takes on is worked out by `Shapes.Prepared`, which is far below here. A
            // module arriving with one has been through a pass that writes into the representation
            // this one answers with.
            throw new IllegalStateException(
                    "`" + m.name() + "` reached resolution having already taken helpers on");
        }
        return new Resolution(
                new Hir.Module(m.name(), m.exposing(), exposedOutputs,
                        r.imports(m), defs, behaviors, fns, List.of(), examples, fakes,
                        m.exampleFileTarget(), m.pos()),
                new ResolutionIndex(List.copyOf(r.denotations), List.copyOf(r.values0),
                        Map.copyOf(r.binders)),
                List.copyOf(r.unresolved), Map.copyOf(declarations));
    }

    /**
     * The import lines, carried across unchanged.
     *
     * <p>An import writes a module name and the names it brings in, and neither is a reference
     * occurrence: what a name brought in denotes is decided where it is used, not here. So there is
     * nothing to answer, and this is the boundary copying a form that says the same thing on both
     * sides of it.
     */
    private List<Hir.Import> imports(Ast.Module m) {
        List<Hir.Import> out = new ArrayList<>();
        for (Ast.Import i : m.imports()) {
            List<Hir.ImportedName> names = new ArrayList<>();
            for (Ast.ImportedName n : i.importedNames()) {
                names.add(new Hir.ImportedName(n.written()));
            }
            out.add(new Hir.Import(i.module(), i.alias(), names, i.pos()));
        }
        for (Map.Entry<String, Set<String>> e : borrowed.entrySet()) {
            Set<String> already = new LinkedHashSet<>();
            for (Ast.Import i : m.imports()) {
                if (i.module().equals(e.getKey())) {
                    already.addAll(i.names());
                }
            }
            List<Hir.ImportedName> names = new ArrayList<>();
            for (String bare : e.getValue()) {
                if (!already.contains(bare)) {
                    // No position on a synthesized name: nobody wrote it on an import list. The
                    // qualified reference that asked for it is where it came from, and that is
                    // already the position of the import as a whole.
                    names.add(new Hir.ImportedName(bare, null));
                }
            }
            if (!names.isEmpty()) {
                out.add(new Hir.Import(e.getKey(), null, names, borrowedAt.get(e.getKey())));
            }
        }
        return out;
    }

    /** The stages of a {@code >->} composition, each answered against the behavior namespace. */
    private List<Hir.Var> stages(List<Ast.Var> stages) {
        List<Hir.Var> out = new ArrayList<>();
        for (Ast.Var stage : stages) {
            out.add(stage(stage));
        }
        return out;
    }

    /** The names a {@code depends on} clause writes. */
    private List<Hir.Var> required(List<Ast.Var> refs, String by) {
        List<Hir.Var> out = new ArrayList<>();
        for (Ast.Var ref : refs) {
            out.add(required(ref, by));
        }
        return out;
    }

    // --- the behavior namespace: a pipeline's stages and a spec's dependencies ---

    /**
     * A {@code >->} stage. {@code X.decoder} / {@code X.encoder} name a codec, which is a boundary
     * edge rather than a behavior (spec §sequential-composition) — said here, where the question is
     * what the name denotes, so nothing further down has a spelling to test for it.
     */
    private Hir.Var stage(Ast.Var ref) {
        if (namesABoundaryEdge(ref.name())) {
            return noBehavior(ref, CompileException.of(Diagnostic
                    .at(ref.pos()).say(new BehaviorMessage.ABoundaryEdgeIsNotAStage()).build()));
        }
        return behaviorNamed(ref, this::unknownBehavior);
    }

    /**
     * Whether a qualified spelling names a codec rather than a behavior — {@code X.decoder},
     * {@code X.encoder}, which are boundary edges (spec §sequential-composition).
     *
     * <p>Only a qualified one: {@code decoder} on its own is an ordinary name, and a module may
     * declare a behavior by it. Asked here and by whatever works out which modules a header reaches,
     * so that a codec's qualifier is not read as a module by one of them and as a type by the other.
     */
    public static boolean namesABoundaryEdge(String written) {
        int dot = written.lastIndexOf('.');
        String last = dot < 0 ? "" : written.substring(dot + 1);
        return last.equals("decoder") || last.equals("encoder");
    }

    /**
     * A name a {@code depends on} clause writes. It must name an injection target, and whether the
     * behavior it names is one is the check's to say (E1607); that nothing declares the name at all
     * is settled here, in the same message, because it is the same question — what does this name
     * denote — asked of a clause rather than of a stage.
     */
    private Hir.Var required(Ast.Var ref, String by) {
        return behaviorNamed(ref, (name, candidates) -> CompileException.of(Diagnostic
                .at(name.written().reportedAt())
                .suggestion(Suggest.candidate(name.name(), candidates))
                .hint(new DeclarationMessage.DeclareItHereOrImportIt(name.name()))
                .say(new DeclarationMessage.DependsOnNamesNoSuchBehavior(by, name.name())).build()));
    }

    /** A name that must denote a behavior, with what to say when none does. */
    private Hir.Var behaviorNamed(Ast.Var ref, Unknown unknown) {
        String written = ref.name();
        int dot = written.lastIndexOf('.');
        if (dot < 0) {
            return bareBehavior(ref, written, unknown);
        }
        String bare = written.substring(dot + 1);
        String qualifier = written.substring(0, dot);
        if (Prelude.isQualifier(qualifier)) {
            // a standard-library qualifier names a function, and a function is not a behavior
            return noBehavior(ref, unknown.report(ref, Set.of()));
        }
        String target = symbols.scope().moduleOfQualifier(qualifier);
        if (target == null) {
            target = qualifier;
        }
        if (target.equals(values.module())) {
            return bareBehavior(ref, bare, unknown);   // this module, named through itself
        }
        if (!values.elsewhere().hasModule(target)) {
            return noBehavior(ref, CompileException.of(Diagnostic
                    .say(new ModuleMessage.NoModuleOfThatName(qualifier, bare))
                    .at(ref.pos()).build()));
        }
        Set<String> declared = values.elsewhere().behaviorsOf(target);
        if (declared == null) {
            // The module is one this compilation has and could not read. What is wrong with it is
            // reported on its own source; saying anything here sends the author to a file that is
            // fine.
            return unanswered(ref);
        }
        if (!declared.contains(bare)) {
            return noBehavior(ref, unknown.report(ref, declared));
        }
        ValueName.Behavior named = new ValueName.Behavior(target, bare);
        // A behavior named through its module is reached through an import, whether or not the
        // author wrote one: the borrowed signature and the injected field are found by it.
        borrowed.computeIfAbsent(target, k -> new LinkedHashSet<>()).add(bare);
        borrowedAt.putIfAbsent(target, ref.pos());
        return behaviorReached(ref, named);
    }

    /** A bare name: this module's own behavior, or one an import brought in. */
    private Hir.Var bareBehavior(Ast.Var ref, String written, Unknown unknown) {
        ValueName.Behavior named = values.behaviors().get(written);
        if (named != null) {
            return behaviorReached(ref, named);
        }
        if (!values.behaviorsWhole()) {
            // An import that could not be followed may have been where this name came from.
            // Whatever is wrong with that module is reported there.
            return unanswered(ref);
        }
        return noBehavior(ref, unknown.report(ref, values.behaviors().keySet()));
    }

    /**
     * {@code ref} denoting {@code name}, and reached as this module reaches it.
     *
     * <p>Both answers together, from the one place that has them. A behavior is reached by the name
     * written here — bare, or under the module a qualified reference names.
     */
    private Hir.Var behaviorReached(Ast.Var ref, ValueName.Behavior name) {
        answered(ref.written(), name);
        return new Hir.Var.Denoting(ref.written(), name,
                ReachName.of(name, ref.name(), values.module()), ref.region());
    }

    /** What to say about a name no behavior answers to, given the names that were reachable. */
    private interface Unknown {
        CompileException report(Ast.Var ref, Set<String> candidates);
    }

    private CompileException unknownBehavior(Ast.Var ref, Set<String> candidates) {
        WrittenName written = ref.written();
        String name = written.canonical();
        return CompileException.of(Diagnostic
                .at(written.reportedAt())
                .suggestion(Suggest.candidate(name, candidates))
                .say(new NameMessage.NoBehaviorOfThatNameInThisPipeline(written.quoted())).build());
    }

    /** Records why a name denotes no behavior, and gives it the name that says so. */
    private Hir.Var noBehavior(Ast.Var ref, CompileException why) {
        nothing(why);
        return unanswered(ref);
    }

    /** A reference resolution read and found nothing for, keeping where it was written. */
    private static Hir.Var unanswered(Ast.Var ref) {
        return new Hir.Var.Unanswered(ref.written(), ref.region());
    }

    private Hir.FnDef fn(Ast.FnDef f) {
        owner = ownerOfValue(f.name());
        List<Hir.FnParam> params = new ArrayList<>();
        Bindings bound = Bindings.NONE;
        for (Ast.FnParam p : f.params()) {
            Answered a = bind(bound, p.binder());
            params.add(new Hir.FnParam(a.binder(), paramType(p.type()), p.typeFromPattern()));
            bound = a.bound();
        }
        Hir.FnBody body = switch (f.body()) {
            case Ast.FnBody.Written w -> new Hir.FnBody.Written(expr(w.expr(), bound));
            case Ast.FnBody.Intrinsic i -> new Hir.FnBody.Intrinsic(i.key());
        };
        return new Hir.FnDef(f.written(), f.declaredIn(), params, retType(f.declaredReturn()), body,
                new Hir.Modifiers(f.modifiers().partial(), f.modifiers().isPrivate()), f.pos());
    }

    // --- written types ---

    private List<Hir.Param> params(List<Ast.Param> params) {
        List<Hir.Param> out = new ArrayList<>();
        for (Ast.Param p : params) {
            out.add(new Hir.Param(p.written(), retType(p.type())));
        }
        return out;
    }

    /** A declaration's invariant clauses, each read against the fields it constrains. */
    private List<Hir.InvariantClause> clauses(List<Ast.InvariantClause> clauses, Bindings bound) {
        List<Hir.InvariantClause> out = new ArrayList<>();
        for (Ast.InvariantClause clause : clauses) {
            out.add(new Hir.InvariantClause(clause.name(), expr(clause.expr(), bound),
                    clause.pos(), clause.region()));
        }
        return out;
    }

    private List<Hir.Field> fields(List<Ast.Field> fields) {
        List<Hir.Field> out = new ArrayList<>();
        for (Ast.Field f : fields) {
            out.add(new Hir.Field(f.written(), typeTerm(f.type())));
        }
        return out;
    }

    private Hir.RetType paramType(Ast.RetType t) {
        return retType(t);
    }

    private Hir.RetType retType(Ast.RetType ret) {
        if (ret == null) {
            return null;
        }
        List<Hir.TypeTerm> cases = new ArrayList<>();
        for (Ast.TypeTerm c : ret.cases()) {
            cases.add(typeTerm(c));
        }
        return new Hir.RetType(cases, ret.pos());
    }

    private Hir.TypeTerm typeTerm(Ast.TypeTerm t) {
        return switch (t) {
            case null -> null;
            case Ast.TypeRef ref -> typeRef(ref);
            case Ast.FnType ft -> {
                List<Hir.RetType> ps = new ArrayList<>();
                for (Ast.RetType p : ft.params()) {
                    ps.add(retType(p));
                }
                yield new Hir.FnType(ps, retType(ft.result()), ft.pos());
            }
        };
    }

    /** A written type reference, with what it denotes decided here — once, and in the module that
     * wrote it, so no later reader has to know where it was written. */
    private Hir.TypeRef typeRef(Ast.TypeRef ref) {
        if (ref == null) {
            return null;
        }
        Hir.TypeTerm arg = typeTerm(ref.arg());
        List<Hir.TypeTerm> elems = null;
        if (ref.tupleElems() != null) {
            elems = new ArrayList<>();
            for (Ast.TypeTerm e : ref.tupleElems()) {
                elems.add(typeTerm(e));
            }
        }
        TypeOps.Reference parts = new TypeOps.Reference(ref.written(), arg, elems, ref.anchor());
        Hir.TypeRef denoted = new Hir.TypeRef(ref.written(), arg, elems, typeOf(parts), ref.anchor());
        // A reference with no name is a tuple or a container shape, which names no declaration.
        if (denoted.name() != null && denoted.pos() != null) {
            switch (symbols.scope().resolve(denoted.written())) {
                case Denotation.Denotes d ->
                        denotations.add(new TypeUse(denoted.written(), d.type()));
                case Denotation.StandsForNothing ignored -> failed++;
                case Denotation.NotInScope ignored -> { }
            }
        }
        return denoted;
    }

    // --- definitions ---

    /** {@code def} resolved as {@code declared}, which is the identity the module's declarations
     * were indexed under and is handed in rather than worked out here. */
    private Hir.Def def(TypeSymbol declared, Ast.Def def) {
        owner = new BindingOwner.OfData(declared);
        return switch (def) {
            case Ast.UnitData u -> new Hir.UnitData(u.written(), declared, u.pos());
            // an invariant reads the fields of the data it belongs to, which are what bind its
            // names — `value > 0` is about this declaration's `value`, whatever else is in scope
            case Ast.Data d -> {
                declareFields(d, declared);
                yield new Hir.Data(d.written(), declared, d.newtype(), names(d.includes()),
                        fields(d.fields()),
                        clauses(d.invariants(), boundFields(d, declared)),
                        d.decoder().map(this::decoder), d.encoder().map(this::encoder),
                        d.pos());
            }
            case Ast.SumData s -> new Hir.SumData(s.written(), declared, sumCases(s),
                    s.decoder().map(this::discriminate),
                    s.encoder().map(this::sumEncoder), s.pos());
        };
    }

    /** A sum's cases keep their own message: {@code data X = A | B} names the cases of one type, so a
     * name nothing declares is answered against that sum rather than as a bare unknown type. */
    private List<Hir.Name> sumCases(Ast.SumData s) {
        List<Hir.Name> out = new ArrayList<>();
        for (Ast.Name c : s.cases()) {
            Denotation answer = symbols.scope().resolve(c.name());
            if (answer instanceof Denotation.NotInScope) {
                throw CompileException.of(Diagnostic
                                .at(s.pos()).say(new BehaviorMessage.UnknownCaseInASum(c.written(), s.name())).build());
            }
            if (answer instanceof Denotation.StandsForNothing) {
                out.add(answered(unanswered(c)));
                continue;
            }
            TypeSymbol denoted = answer.type();
            // Recorded like any other written name. A case is a name this module wrote and this pass
            // answered, so leaving it out made it a use nothing could see — an editor asked about it
            // had no answer, and a reader asking which imports are written found the name missing.
            out.add(answered(denoting(c, denoted)));
        }
        return out;
    }

    /**
     * The fields of a declaration, as the names its own invariant reads — the ones written here and
     * the ones a spread brings in, which are as much this declaration's fields as the written ones
     * (and are what a spread-in invariant was written against).
     */
    /**
     * Where each field this declaration writes is written, against the binding it introduces inside
     * an invariant.
     *
     * <p>Recorded whether or not this declaration has an invariant of its own: a declaration that
     * includes it reads these fields in <em>its</em> invariant, and the binding a field is stays the
     * declaring declaration's, so this is where an editor is answered from either way.
     */
    private void declareFields(Ast.Data d, TypeSymbol declared) {
        Map<String, BindingId> bindings = TypeOps.fieldBindingsAsWritten(declared, d, symbols);
        for (Ast.Field field : d.fields()) {
            BindingId binding = bindings.get(field.name());
            if (binding != null) {
                binders.put(binding, new BoundName(field.written()));   // OfFields
            }
        }
    }

    private Bindings boundFields(Ast.Data d, TypeSymbol declared) {
        Bindings bound = Bindings.NONE;
        // which binding each field is is answered in one place, so the pass that emits this
        // invariant reaches the same ones without working them out again
        for (Map.Entry<String, BindingId> f
                : TypeOps.fieldBindingsAsWritten(declared, d, symbols).entrySet()) {
            bound = bound.and(f.getKey(), new ValueName.Local(f.getKey(), f.getValue()));
        }
        return bound;
    }

    private Hir.Discriminate discriminate(Ast.Discriminate d) {
        List<Hir.Variant> variants = new ArrayList<>();
        for (Ast.Variant v : d.variants()) {
            variants.add(new Hir.Variant(v.tag(), type(v.caseType()), v.pos()));
        }
        return new Hir.Discriminate(d.key(), variants, d.pos());
    }

    private Hir.SumEncoder sumEncoder(Ast.SumEncoder e) {
        List<Hir.EncVariant> variants = new ArrayList<>();
        for (Ast.EncVariant v : e.variants()) {
            variants.add(new Hir.EncVariant(type(v.caseType()), v.tag(), v.pos()));
        }
        return new Hir.SumEncoder(e.key(), variants, e.pos());
    }

    // --- decoders ---

    /** A decoder reads the value it is decoding under the name it gives it, and an object decoder
     * reads what each of its binds took out of the object. Those are what bind its names. */
    private Hir.DecoderDef decoder(Ast.DecoderDef d) {
        return switch (d) {
            case Ast.PrimDecoder p -> {
                Answered input = bind(Bindings.NONE, p.input());
                Bindings bound = input.bound();
                List<Hir.DecStmt> stmts = new ArrayList<>();
                for (Ast.DecStmt s : p.stmts()) {
                    Ast.Let let = (Ast.Let) s;
                    Hir.Expr value = expr(let.value(), bound);
                    Answered a = bind(bound, let.binder());
                    stmts.add(new Hir.Let(a.binder(), value, let.pos()));
                    bound = a.bound();
                }
                yield new Hir.PrimDecoder(Hir.RawKind.valueOf(p.from().name()), input.binder(), stmts,
                        construct(p.result(), bound), p.pos());
            }
            case Ast.ObjectDecoder o -> {
                List<Hir.Bind> binds = new ArrayList<>();
                Bindings bound = Bindings.NONE;
                for (Ast.Bind b : o.binds()) {
                    Answered a = bind(bound, b.binder());
                    binds.add(new Hir.Bind(a.binder(), b.key(), decRef(b.ref()), b.pos()));
                    bound = a.bound();
                }
                yield new Hir.ObjectDecoder(binds, construct(o.result(), bound), o.pos());
            }
            case Ast.NewtypeDecoder n -> {
                Answered input = bind(Bindings.NONE, n.input());
                yield new Hir.NewtypeDecoder(decRef(n.inner()), input.binder(),
                        construct(n.result(), input.bound()), n.pos());
            }
        };
    }

    private Hir.DecRef decRef(Ast.DecRef ref) {
        return switch (ref) {
            case Ast.DecRef.Bare b -> bareDecRef(b);
            case Ast.OptionDecRef o -> new Hir.OptionDecRef(bareDecRef(o.element()), o.pos());
        };
    }

    /** Resolving keeps the shape it was given, so what an optional holds stays what an optional may
     *  hold. Split here for that reason and not to say anything new about the arms. */
    private Hir.DecRef.Bare bareDecRef(Ast.DecRef.Bare ref) {
        return switch (ref) {
            case Ast.PrimDecRef p -> new Hir.PrimDecRef(p.kind(), p.pos());
            case Ast.DataDecRef d -> new Hir.DataDecRef(type(d.typeName()), d.pos());
            case Ast.ListDecRef l -> new Hir.ListDecRef(decRef(l.element()), l.pos());
            case Ast.SetDecRef s -> new Hir.SetDecRef(decRef(s.element()), s.pos());
            // the key is already the classification the checker made, carrying a resolved name
            case Ast.MapDecRef m -> new Hir.MapDecRef(decRef(m.value()), m.key(), m.pos());
        };
    }

    private Hir.Construct construct(Ast.Construct c, Bindings bound) {
        List<Hir.FieldInit> inits = new ArrayList<>();
        for (Ast.FieldInit i : c.inits()) {
            inits.add(new Hir.FieldInit(i.written(), expr(i.value(), bound)));
        }
        return new Hir.Construct(type(c.typeName()), inits, c.pos());
    }

    // --- encoders ---

    /** An encoder reads the value it is encoding under the name it gives it. */
    private Hir.EncoderDef encoder(Ast.EncoderDef e) {
        Answered self = bind(Bindings.NONE, e.self());
        return new Hir.EncoderDef(self.binder(), rawExpr(e.result(), self.bound()), e.pos());
    }

    private Hir.RawExpr rawExpr(Ast.RawExpr r, Bindings bound) {
        return switch (r) {
            case Ast.TextRaw t -> new Hir.TextRaw(expr(t.arg(), bound), t.pos());
            case Ast.IntRaw i -> new Hir.IntRaw(expr(i.arg(), bound), i.pos());
            case Ast.BoolRaw b -> new Hir.BoolRaw(expr(b.arg(), bound), b.pos());
            case Ast.DecimalRaw d -> new Hir.DecimalRaw(expr(d.arg(), bound), d.pos());
            case Ast.IsoTextRaw i -> new Hir.IsoTextRaw(expr(i.arg(), bound), i.pos());
            case Ast.EncodeRaw en ->
                    new Hir.EncodeRaw(type(en.typeName()), expr(en.arg(), bound), en.pos());
            case Ast.ListEnc l -> new Hir.ListEnc(expr(l.source(), bound), encElem(l.elem()), l.pos());
            case Ast.SetEnc s -> new Hir.SetEnc(expr(s.source(), bound), encElem(s.elem()), s.pos());
            case Ast.MapEnc m -> new Hir.MapEnc(expr(m.source(), bound), encElem(m.elem()),
                    m.key(), m.pos());
            // the inner expression reads the element the option holds, under the name given here
            case Ast.OptionRaw o -> {
                Answered elem = bind(bound, o.elem());
                yield new Hir.OptionRaw(expr(o.access(), bound),
                        rawExpr(o.inner(), elem.bound()), elem.binder(), o.pos());
            }
            case Ast.ObjectRaw o -> {
                List<Hir.RawEntry> entries = new ArrayList<>();
                for (Ast.RawEntry entry : o.entries()) {
                    entries.add(new Hir.RawEntry(entry.key(), rawExpr(entry.value(), bound),
                            entry.pos()));
                }
                yield new Hir.ObjectRaw(entries, o.pos());
            }
        };
    }

    private Hir.EncElem encElem(Ast.EncElem e) {
        return switch (e) {
            case Ast.EncElem.Bare b -> bareEncElem(b);
            case Ast.OptionElemEnc o -> new Hir.OptionElemEnc(bareEncElem(o.elem()), o.pos());
        };
    }

    private Hir.EncElem.Bare bareEncElem(Ast.EncElem.Bare e) {
        return switch (e) {
            case Ast.PrimEnc p -> new Hir.PrimEnc(p.kind(), p.pos());
            case Ast.DataEnc d -> new Hir.DataEnc(type(d.typeName()), d.pos());
            case Ast.ListElemEnc l -> new Hir.ListElemEnc(encElem(l.elem()), l.pos());
            case Ast.SetElemEnc s -> new Hir.SetElemEnc(encElem(s.elem()), s.pos());
            case Ast.MapElemEnc m -> new Hir.MapElemEnc(encElem(m.value()), m.key(), m.pos());
        };
    }

    // --- expressions ---

    private Hir.Expr expr(Ast.Expr e) {
        return expr(e, Bindings.NONE);
    }

    /**
     * Rewrites the names {@code e} itself writes, against the bindings in force where it is written.
     *
     * <p>Every kind is named here. Between the two representations there is no rewrite that carries
     * a node across on its own, so a node this pass does not know how to answer is a node it cannot
     * answer at all — and an expression kind added later stops the build here, which is the one
     * place it has to be accounted for.
     */
    private Hir.Expr expr(Ast.Expr e, Bindings bound) {
        return switch (e) {
            case Ast.Var v -> reached(v, bound);
            // Applying a name is answered as a name: which of a binding, a helper, a library
            // function or a type it is decides what the application means. Applying anything else
            // is answered as the expression it is, and what may be applied is the check's to say.
            case Ast.Apply call when call.appliesAName() -> applied(call, bound);
            case Ast.Apply call -> new Hir.Apply(callee(call.function(), bound),
                    exprs(call.args(), bound), call.origin(), call.appliedAs(), call.pos(),
                    call.region());
            // `Map.empty`, `String.isEmpty`, `up.Amount` — a namespace and a member of it, which
            // the parser read as a field taken off a name because it reads no case at all. Folded
            // here and nowhere earlier: `Map` may be a parameter, and a binding in force wins over
            // everything else — which is a fact the parser and the AST builder do not have.
            case Ast.FieldAccess fa -> {
                Hir.Var member = qualifiedName(fa, false, bound);
                yield member != null ? member
                        : new Hir.FieldAccess(expr(fa.target(), bound), fa.name(), fa.pos(),
                                fa.region());
            }
            // the type being built is this case's business; everything under it is a slot like any
            // other
            // A construction written in a row does not write out an optional field it leaves
            // absent; one written anywhere else says what each of its fields is.
            case Ast.NewData nd -> new Hir.NewData(type(nd.typeName()), inits(nd.inits(), bound),
                    vars(nd.spreads(), bound), nd.origin(),
                    inARow ? Hir.Fields.OPTIONALS_MAY_BE_OMITTED : Hir.Fields.EVERY_ONE_WRITTEN,
                    nd.pos(), nd.region());
            // a binding's pattern may write Option's `Some`, which the binding check then rejects
            // for what it is — a name that opens nothing — rather than as a name nothing declares
            case Ast.LetIn li -> {
                Hir.Expr value = expr(li.value(), bound);
                Answered a = bind(bound, li.binder());
                yield new Hir.LetIn(a.binder(), value,
                        paramType(li.declaredType()), li.annotated(),
                        li.opens() == null ? null : caseName(li.opens()),
                        expr(li.body(), a.bound()), li.pos(), li.region());
            }
            case Ast.Block b -> {
                AnsweredAll ps = bindAll(bound, b.params());
                yield new Hir.Block(ps.binders(), expr(b.body(), ps.bound()), b.pos(), b.region());
            }
            // an attempt's binder names the value only where there is one to name — the success
            // branch. The construction and the else value are outside it.
            case Ast.IfConstructed ic -> {
                Answered a = bind(bound, ic.binder());
                yield new Hir.IfConstructed(expr(ic.construct(), bound), a.binder(),
                        expr(ic.then(), a.bound()), arms(ic.els(), bound), ic.origin(), ic.pos(),
                        ic.region());
            }
            case Ast.Match m -> {
                List<Hir.Case> cases = new ArrayList<>();
                for (Ast.Case c : m.cases()) {
                    Answered a = c.binding() == null ? null : bind(bound, c.binding());
                    Bindings inArm = a == null ? bound : a.bound();
                    cases.add(new Hir.Case(caseNames(c.caseTypes()),
                            a == null ? null : a.binder(), expr(c.body(), inArm),
                            c.unwrapAsserts() == null ? null : names(c.unwrapAsserts()), c.pos()));
                }
                yield new Hir.Match(expr(m.scrutinee(), bound), cases, m.origin(), m.pos(), m.region());
            }
            case Ast.IntLit x -> new Hir.IntLit(x.value(), x.pos(), x.region());
            case Ast.DecimalLit x -> new Hir.DecimalLit(x.value(), x.pos(), x.region());
            case Ast.StringLit x -> new Hir.StringLit(x.value(), x.pos(), x.region());
            case Ast.BoolLit x -> new Hir.BoolLit(x.value(), x.pos(), x.region());
            case Ast.Unreachable x -> new Hir.Unreachable(x.reason(), x.pos(), x.region());
            case Ast.Neg x -> new Hir.Neg(expr(x.operand(), bound), x.pos(), x.region());
            case Ast.Binary x -> new Hir.Binary(Hir.BinOp.valueOf(x.op().name()),
                    expr(x.left(), bound), expr(x.right(), bound), x.origin(), x.pos(), x.region());
            case Ast.If x -> new Hir.If(expr(x.cond(), bound), expr(x.then(), bound),
                    expr(x.els(), bound), x.origin(), x.pos(), x.region());
            case Ast.ListLit x -> inARow
                    ? new Hir.RowCollection(exprs(x.elements(), bound), x.pos(), x.region())
                    : new Hir.ListLit(exprs(x.elements(), bound), x.pos(), x.region());
            case Ast.ListComp x -> new Hir.ListComp(expr(x.element(), bound),
                    exprs(x.guards(), bound), x.origin(), x.pos(), x.region());
            case Ast.Tuple x -> new Hir.Tuple(exprs(x.elements(), bound), x.pos(), x.region());
            case Ast.TupleGet x -> new Hir.TupleGet(expr(x.tuple(), bound), x.index(), x.arity(),
                    x.pos(), x.region());
            // An expansion is what the inliner writes, and the inliner runs on what this pass
            // answers. One here is a tree that has been below this boundary and come back.
            case Ast.Expansion x -> throw new IllegalStateException(
                    "an expansion reached resolution at " + x.pos());
        };
    }

    /** A construction's field values, each a slot like any other. */
    private List<Hir.FieldInit> inits(List<Ast.FieldInit> inits, Bindings bound) {
        List<Hir.FieldInit> out = new ArrayList<>();
        for (Ast.FieldInit i : inits) {
            out.add(new Hir.FieldInit(i.written(), expr(i.value(), bound)));
        }
        return out;
    }

    /** The names in a construction's spreads — a name slot, where only a name may stand. */
    private List<Hir.Var> vars(List<Ast.Var> vars, Bindings bound) {
        List<Hir.Var> out = new ArrayList<>();
        for (Ast.Var v : vars) {
            out.add(name(v, bound));
        }
        return out;
    }

    /**
     * One name in the value namespace, answered against the bindings in force where it is written —
     * what this pass does at a name slot, wherever a node has one. A binding in force wins over a
     * declaration in a spread as everywhere else.
     *
     */
    private Hir.Var name(Ast.Var written, Bindings bound) {
        return reached(written, bound);
    }

    /** An application of a name, with what the name denotes and how this module reaches it answered
     * here — the same pair, from the same place, as a name standing on its own. */
    private Hir.Expr applied(Ast.Apply call, Bindings bound) {
        ValueName denotes = calledName(call, bound);
        // Answered rather than rebuilt: what the callee means is settled here and where it is
        // written is not this pass's to decide. Building one from the name would take its extent
        // from the characters that spell it, which is short of what a parenthesized callee covers.
        WrittenName written = call.function() instanceof Ast.Var applied ? applied.written()
                : call.name();
        Region over = call.function() instanceof Ast.Var applied ? applied.region()
                : written.region();
        Hir.Var name;
        if (denotes == null) {
            name = new Hir.Var.Unanswered(written, over);
        } else {
            answered(call.name(), denotes);
            name = new Hir.Var.Denoting(written, denotes,
                    ReachName.of(denotes, call.written(), values.module()), over);
        }
        return new Hir.Apply(name, exprs(call.args(), bound), call.origin(), call.appliedAs(),
                call.pos(), call.region());
    }

    /**
     * {@code v} with what it denotes and the name this module reaches it by, both answered here.
     *
     * <p>The two together, and only here: which module is doing the reading is what decides the reach
     * name, and this pass is the last place that has it. A pass downstream working it out from the
     * spelling would answer differently depending on which rewrites had run — which is the defect
     * this carries the answer to avoid.
     */
    private Hir.Var reached(Ast.Var v, Bindings bound) {
        ValueName denotes = valueName(v.written(), bound);
        if (denotes == null) {
            return new Hir.Var.Unanswered(v.written(), v.region());
        }
        answered(v.written(), denotes);
        return new Hir.Var.Denoting(v.written(), denotes,
                ReachName.of(denotes, v.name(), values.module()), v.region());
    }

    private List<Hir.ElseArm> arms(List<Ast.ElseArm> arms, Bindings bound) {
        List<Hir.ElseArm> out = new ArrayList<>();
        for (Ast.ElseArm arm : arms) {
            out.add(new Hir.ElseArm(arm.clause(), expr(arm.body(), bound), arm.pos()));
        }
        return out;
    }

    private List<Hir.Expr> exprs(List<Ast.Expr> es) {
        return exprs(es, Bindings.NONE);
    }

    private List<Hir.Expr> exprs(List<Ast.Expr> es, Bindings bound) {
        List<Hir.Expr> out = new ArrayList<>();
        for (Ast.Expr e : es) {
            out.add(expr(e, bound));
        }
        return out;
    }

    // --- names in a body ---

    /**
     * What a name written in the value namespace denotes, or null where nothing here does.
     *
     * <p>One ladder, in one order, so a name means the same thing under an application as beside one.
     * It was two — a bare name tried the declared types before this module's helpers, an applied one
     * tried the library first and the types last — and which rung answered therefore depended on
     * whether a `(` followed. The rungs a spelling could reach twice are refused where the value
     * namespace is assembled, so the order between them decides nothing.
     *
     * <p>{@code applied} is the one thing the position still says. A type written as a value is the
     * construction of a unit data and records where it came from; applied, it is a newtype taking
     * what it wraps, and the application is what says that.
     */
    private ValueName lookup(WrittenName name, boolean applied, Bindings bound) {
        String written = name.canonical();
        // a binding in force wins over everything else: a body may bind a name a module declares,
        // and the binding is what the name means there
        ValueName.Local binding = bound.binderOf(written);
        if (binding != null) {
            return binding;
        }
        // names the language itself gives: Option's two cases
        if (written.equals("None") || written.equals("Some")) {
            return new ValueName.Builtin(written);
        }
        // A library qualifier makes this a library reference — `Date(...)`, whose namespace is the
        // whole name, included. Whether the library has a member of that name is the check's to say:
        // asking here would tie the answer to how much of the library has been loaded, and the
        // library resolves its own sources while it loads.
        //
        // A `private` declaration is the exception, and asking about it here is safe for the same
        // reason: the only modules that may name one are the library's own, and they are told yes
        // without the entry being looked up at all.
        // Split off what the author wrote, which is where a library name enters the compiler as two
        // values: the qualifier they typed and the operation they asked of it. Nothing downstream
        // splits it again — from here it is carried as the pair.
        int dot = written.lastIndexOf('.');
        if (Prelude.isQualifier(dot < 0 ? written : written.substring(0, dot))) {
            if (Reserved.isNamespace(values.module()) || !Prelude.isPrivateMember(written)) {
                return dot < 0 ? ValueName.Stdlib.namespace(written)
                        : new ValueName.Stdlib(written.substring(0, dot), written.substring(dot + 1));
            }
            return null;
        }
        if (symbols.scope().resolve(name) instanceof Denotation.Denotes d) {
            return new ValueName.OfType(written, d.type(),
                    applied ? null : ConstructionOrigin.own());
        }
        // a helper or a behavior, applied or handed over by name — which the inliner expands into a
        // block that applies it
        ValueName.Helper helper = values.helpers().get(written);
        if (helper != null) {
            return helper;
        }
        ValueName.Behavior behavior = values.behaviors().get(written);
        if (behavior != null) {
            return behavior;
        }
        // A name an import let this module write without its qualifier. Asked last: an import brings
        // a name in, and everything the module already has — a binding in force, its own
        // declarations — is what that name means here instead.
        return values.exposed().get(written);
    }

    /**
     * The callee of an application that does not apply a bare name.
     *
     * <p>A field read in this position may be a qualified name — {@code Map.empty(k)},
     * {@code up.Amount(n)} — and it is answered here rather than as a value, because applied is
     * what the position says: a type written as a value is a unit data's construction, and applied
     * it is a newtype taking what it wraps. Anything else is the expression it is, and what may be
     * applied is the check's to say.
     */
    private Hir.Expr callee(Ast.Expr function, Bindings bound) {
        if (function instanceof Ast.FieldAccess fa) {
            Hir.Var name = qualifiedName(fa, true, bound);
            if (name != null) {
                return name;
            }
        }
        return expr(function, bound);
    }

    /**
     * A chain of names read as one qualified name — {@code Map.empty}, {@code up.Amount},
     * {@code probe.a.Amount}, where the module's own name is dotted — or null where it is an
     * ordinary field read.
     *
     * <p>Only where the chain's root is unbound. A parameter or a {@code let} named {@code Map}
     * makes {@code Map.empty} that binding's {@code empty} field, resolved the ordinary way, and no
     * qualified name is produced.
     *
     * <p>The whole chain is asked first, and a chain that answers nothing is left for the caller to
     * take apart — so {@code probe.a.defaultAmount.value} folds {@code probe.a.defaultAmount} and
     * reads {@code .value} off it. What is reported, and where, is
     * {@link #unknownMember}'s to say: a member of a namespace that has no such member is named in
     * full, and a chain rooted at a name nothing declares is reported at that name.
     *
     * <p>Positioned at the root, so what a reader asks about covers every token of the name.
     */
    private Hir.Var qualifiedName(Ast.FieldAccess fa, boolean applied, Bindings bound) {
        Ast.Var root = rootName(fa);
        if (root == null || bound.binderOf(root.name()) != null) {
            return null;
        }
        WrittenName written = dottedName(fa);
        ValueName denotes = lookup(written, applied, bound);
        if (denotes != null) {
            ValueName resolved = answered(written, denotes);
            return new Hir.Var.Denoting(written, resolved,
                    ReachName.of(resolved, written.canonical(), values.module()),
                    written.region());
        }
        return unknownMember(fa, written, applied, bound);
    }

    /**
     * The report for a chain whose spelling denotes nothing, or null where there is nothing to say
     * here and the chain is taken apart instead.
     *
     * <p>Something is said only where the part in front is a namespace: {@code probe.a.NoSuch}
     * names a module that exists and a member it has not got, and reporting the root {@code probe}
     * as an unknown identifier would send the author after a module name that is right. Where the
     * front is not a namespace — {@code unknown.member} — nothing is said, and the root is reported
     * as the unknown identifier it is once the chain is read as the field access it turned out to
     * be.
     */
    private Hir.Var unknownMember(Ast.FieldAccess fa, WrittenName written, boolean applied,
                                  Bindings bound) {
        WrittenName qualifier = dottedName(fa.target());
        if (qualifier == null || !isNamespace(qualifier.canonical())) {
            return null;
        }
        nothing(unknownIdentifier(written, bound));
        return new Hir.Var.Unanswered(written, written.region());
    }

    /** Whether {@code qualifier} names a namespace a member may be reached through: a
     *  standard-library one, or a module of this compilation (or an alias for one). */
    private boolean isNamespace(String qualifier) {
        return Prelude.isQualifier(qualifier) || symbols.scope().moduleOfQualifier(qualifier) != null;
    }

    /** The name a chain of field reads is rooted at, or null where it is rooted at anything else —
     *  a call's result, a parenthesised expression — which no qualified name can be. */
    private static Ast.Var rootName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v;
            case Ast.FieldAccess fa -> rootName(fa.target());
            default -> null;
        };
    }

    /** The dotted spelling of a chain of names, or null where it is not one. */
    private static WrittenName dottedName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.written();
            case Ast.FieldAccess fa -> {
                WrittenName target = dottedName(fa.target());
                yield target == null ? null : target.then(fa.name());
            }
            default -> null;
        };
    }

    /** What a name used as a value denotes, or null where nothing does — reported here. */
    private ValueName valueName(WrittenName written, Bindings bound) {
        ValueName denotes = lookup(written, false, bound);
        return denotes != null ? denotes : nothing(unknownIdentifier(written, bound));
    }

    /**
     * The same, for the name an application applies.
     *
     * <p>How the lookup is made differs — an application may reach what a bare name may not — and
     * what a miss means does not. A name that resolved to nothing resolved to nothing, and the
     * position it was written in is a fact about the source rather than about the name.
     */
    private ValueName calledName(Ast.Apply call, Bindings bound) {
        ValueName denotes = lookup(call.name(), true, bound);
        return denotes != null ? denotes : nothing(unknownIdentifier(call.name(), bound));
    }

    /**
     * Records what a name used as a value was answered with, and hands it back.
     *
     * <p>A name that denotes a type — a unit data written as a value, a newtype applied to what it
     * wraps — is a use of that type as much as one written in a field's type is, and is recorded as
     * one too. Otherwise renaming the type would rewrite every other mention of it and leave these,
     * which is a rename that stops the workspace compiling.
     *
     * <p>A name nothing answered to is recorded nowhere. What this collects is what the pass worked
     * out, and it did not work that one out: the name it carries stands for the absence so that the
     * traversal can go on past it, and a reader handed that name back would be told a binding is
     * there under a spelling nothing binds.
     */
    private ValueName answered(WrittenName written, ValueName denotes) {
        if (written.pos() == null) {
            return denotes;
        }
        values0.add(new ValueUse(written, denotes));
        if (denotes instanceof ValueName.OfType named) {
            denotations.add(new TypeUse(written, named.type()));
        }
        return denotes;
    }

    /**
     * Records that a name in a body denotes nothing, and answers with nothing.
     *
     * <p>The name that carries this is {@link Ast.Var.Unanswered}, built where the reference is:
     * a stand-in identity handed back here would say a binding is there under a spelling nothing
     * binds, and every reader below would have to know not to believe it.
     */
    private ValueName nothing(CompileException why) {
        unresolved.add(why);
        failed++;
        return null;
    }

    /** The names a body could have written where it wrote one nothing answers to. */
    private List<String> reachable(Bindings bound) {
        List<String> names = new ArrayList<>(bound.byName().keySet());
        names.addAll(values.helpers().keySet());
        names.addAll(values.behaviors().keySet());
        return names;
    }

    /**
     * The report for a spelling under a library qualifier that the library has no member for, or
     * null where the spelling is not one. A {@code private} declaration lands here: from outside the
     * reserved namespace the library has no such member, which is what a caller is told — the same
     * answer a misspelling gets, because from where the caller stands they are the same thing.
     */
    private CompileException notALibraryMember(WrittenName written) {
        String name = written.canonical();
        int dot = name.lastIndexOf('.');
        if (dot < 0 || !Prelude.isQualifier(name.substring(0, dot))) {
            return null;
        }
        return CompileException.of(Diagnostic
                        .at(written.reportedAt()).say(new NameMessage.NotAStandardLibraryFunction(written.quoted())).build());
    }

    private CompileException unknownIdentifier(WrittenName written, Bindings bound) {
        String name = written.canonical();
        if (name.equals("null")) {
            return CompileException.of(Diagnostic.at(written.reportedAt()).say(new DeclarationMessage.NullIsNotPartOfTheLanguage()).build());
        }
        CompileException notALibraryMember = notALibraryMember(written);
        if (notALibraryMember != null) {
            return notALibraryMember;
        }
        // Asked here as well as of a call, because what the library publishes is not only functions:
        // `Map.empty` is a value, and a function's own name is a value where it is handed over. A
        // nearby binding is the wrong answer for any of them — the name exists and is reached.
        CompileException bareLibraryName = StdlibNames.writtenBare(written.quoted(), name,
                written.region());
        if (bareLibraryName != null) {
            return bareLibraryName;
        }
        List<String> candidates = reachable(bound);
        Diagnostic.Builder report = Diagnostic
                .at(written.reportedAt())
                .suggestion(Suggest.candidate(name, candidates));
        // A name another module of this compilation exposes is the one kind of unresolved name that
        // has somewhere to go, and it is what a name left off an import list looks like from here.
        // Said as what is known — that module has it — rather than as an instruction, since reaching
        // it qualified needs no import at all.
        String elsewhere = written.canonical().indexOf('.') < 0
                ? symbols.scope().moduleExposing(name) : null;
        if (elsewhere != null) {
            report = report.hint(new NameMessage.ItIsExposedByAnotherModule(elsewhere, name));
        }
        return CompileException.of(report.say(new NameMessage.NoValueOfThatNameInScope(written.quoted())).build());
    }


    /**
     * The names bound at a point in a body, each with the binding it is. Persistent: extending it
     * leaves the outer scope as it was, which is what an inner binding shadowing an outer one is.
     */
    record Bindings(Map<String, ValueName.Local> byName) {

        static final Bindings NONE = new Bindings(Map.of());

        Bindings and(String name, ValueName.Local binding) {
            Map<String, ValueName.Local> next = new HashMap<>(byName);
            next.put(name, binding);
            return new Bindings(Map.copyOf(next));
        }

        ValueName.Local binderOf(String name) {
            return byName.get(name);
        }
    }

    // --- names ---

    private List<Hir.Name> names(List<Ast.Name> names) {
        List<Hir.Name> out = new ArrayList<>();
        for (Ast.Name n : names) {
            out.add(type(n));
        }
        return out;
    }

    private static Hir.Name denoting(Ast.Name n, TypeSymbol type) {
        return new Hir.Name.Denoting(n.name(), type);
    }

    private static Hir.Name unanswered(Ast.Name n) {
        return new Hir.Name.Unanswered(n.name());
    }

    /** A name that must denote a declared type. */
    private Hir.Name type(Ast.Name n) {
        return answered(switch (symbols.scope().resolve(n.name())) {
            case Denotation.Denotes d -> denoting(n, d.type());
            // In scope standing for nothing: a name an import line could not bring in takes the
            // error type rather than being reported as an unknown name at every use. The import
            // line is where that was reported, so nothing more is said here.
            case Denotation.StandsForNothing ignored -> unanswered(n);
            case Denotation.NotInScope ignored -> nothingDenotes(n);
        });
    }

    /** The names a {@code match} arm may write: a declared case, a primitive heading a union
     * ({@code Int} in {@code Int | DivisionByZero}), a runtime error case, or one of Option's two.
     * A declared type wins over Option's names, so a model may still declare {@code Some}. */
    private List<Hir.Name> caseNames(List<Ast.Name> names) {
        List<Hir.Name> out = new ArrayList<>();
        for (Ast.Name n : names) {
            out.add(caseName(n));
        }
        return out;
    }

    private Hir.Name caseName(Ast.Name n) {
        return answered(switch (symbols.scope().resolveCase(n.name())) {
            case Denotation.Denotes d -> denoting(n, d.type());
            case Denotation.StandsForNothing ignored -> unanswered(n);
            case Denotation.NotInScope ignored -> {
                TypeSymbol option = TypeSymbol.optionCase(n.written());
                yield option != null ? denoting(n, option) : nothingDenotes(n);
            }
        });
    }

    /**
     * What a reference denotes, or {@link souther.compiler.types.Type#ERRONEOUS} when nothing does.
     *
     * <p>This pass is where a failure becomes a value. {@link TypeOps#denoted} answers or says it
     * cannot, because it is asked one reference at a time and has nowhere to put a report; here there
     * is somewhere to put it, and a tree to carry on resolving.
     */
    private Type typeOf(TypeOps.Reference ref) {
        try {
            return TypeOps.denoted(ref, symbols);
        } catch (CompileException e) {
            failed++;
            unresolved.add(e);
            return Type.ERRONEOUS;
        }
    }

    /** Reports that nothing declares {@code n}, and hands back the name that says so. */
    private Hir.Name nothingDenotes(Ast.Name n) {
        unresolved.add(TypeOps.unknownType(n.name(), symbols));
        return unanswered(n);
    }

    /** Records what a name was answered with, and hands it back. A name with no position was
     * synthesized by an earlier pass rather than written, so there is nothing to point at, and a
     * name nothing answered is an absence rather than a declaration to record. */
    private Hir.Name answered(Hir.Name n) {
        if (!(n.answered() instanceof Hir.Name.Denoting names)) {
            failed++;
        } else if (n.pos() != null) {
            denotations.add(new TypeUse(n.name(), names.type()));
        }
        return n;
    }
}
