package souther.compiler.sites;

import souther.compiler.Reserved;
import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.BindingEvidence;
import souther.compiler.check.DeclaredTypeEvidence;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Answer;
import souther.compiler.query.Bodies;
import souther.compiler.query.Db;
import souther.compiler.query.Names;
import souther.compiler.query.Sites;
import souther.compiler.source.SourceId;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSpelling;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * What is known about one revision of one module's source, as an editor asks it.
 *
 * <p>The boundary, and the only thing outside the compiler reads. Everything it answers is about an
 * occurrence the source wrote, found by the characters it was written over, and every answer comes
 * from this one revision — nothing here is carried over from a revision that compiled earlier, so an
 * answer is either about what the buffer says now or is absent.
 *
 * <p>Built where it is used and dropped there. It holds a way to reach answers rather than a set of
 * them, which is what {@link Names#derivedSymbols} is and for the same reason: it has no equality to
 * be memoised by, and a caller that kept one would be keeping the compilation it was made from.
 *
 * <p>Absent where the occurrences of the module could not be told apart. What an editor does then is
 * everything it can do from the syntax alone, and nothing that rests on knowing which occurrence a
 * position is. Half of a snapshot is not published. What an individual answer rests on is a separate
 * question: a fact this cannot reach is that fact absent, and not the snapshot going away.
 */
public final class SemanticSnapshot {

    private final Db db;
    private final String module;
    private final AuthoredSites sites;
    private final Symbols symbols;

    private SemanticSnapshot(Db db, String module, AuthoredSites sites, Symbols symbols) {
        this.db = db;
        this.module = module;
        this.sites = sites;
        this.symbols = symbols;
    }

    /**
     * What {@code db} can be asked about {@code module}, or empty where it cannot be asked.
     *
     * <p>Empty rather than partial. A module whose source does not resolve has no settled reading of
     * its names, and one whose occurrences collide has no way to say which occurrence a position is;
     * neither is a snapshot with less in it.
     */
    public static Optional<SemanticSnapshot> of(Db db, String module) {
        Answer<AuthoredSites> occurrences = db.ask(new Sites.Authored(module));
        Answer<Symbols> scope = Names.derivedSymbols(db, module);
        return occurrences.present() && scope.present()
                ? Optional.of(new SemanticSnapshot(db, module, occurrences.value(), scope.value()))
                : Optional.empty();
    }

    /**
     * What the left of the {@code .} is, for the narrowest thing written over {@code cursor}.
     *
     * <p>Empty where no access was written there. That a receiver is a value whose type nothing here
     * states is a different answer and is {@link MemberReceiver.UntypedValue} — a reader that offers
     * nothing for both still knows which of them it was told.
     */
    public Optional<MemberReceiver> memberReceiverAround(SourcePos cursor) {
        return memberReceiverOf(sites.innermostContaining(cursor));
    }

    /**
     * The same, for a caller that has the access's extent rather than a place inside it.
     *
     * <p>Two entry points and not one method that guesses which it was handed. What an editor has is
     * a cursor; what a reader that already walked the tree has is an extent, and an extent that is
     * an occurrence is one occurrence while a place is inside several.
     */
    public Optional<MemberReceiver> memberReceiverOf(Region extent) {
        return switch (sites.written(extent)) {
            // A field taken off a value. That it is one is already settled: the parser reads
            // `m.name` and `x.field` alike, and this is a field read because a binding was in force
            // where the chain is rooted.
            case Hir.FieldAccess access -> Optional.of(valueReceiver(access.target()));
            case Hir.Var written -> namespaceOf(written.written());
            case null, default -> Optional.empty();
        };
    }

    /**
     * How this module writes {@code type}, or empty where it has no name for it.
     *
     * <p>Asked of the module rather than taken off the type. What a declaration is and what a module
     * calls it are two things: a type reached through an import is written the way the import
     * brought it in, and one this module neither declares nor imports has no spelling here at all.
     * Empty is that second answer, and a reader shown a name it cannot write would be shown
     * something to type that does not compile.
     */
    public Optional<String> spellingOf(Type type) {
        return TypeSpelling.of(type, symbols.scope()::reach)
                instanceof TypeSpelling.Spelled(String rendered)
                ? Optional.of(rendered) : Optional.empty();
    }

    /**
     * Whether a value of {@code type} is held to a rule its declaration wrote.
     *
     * <p>A fact about the type and not about any value of it. What it is for is a reader looking at
     * a name whose type is not written beside it: that the type has an invariant is the difference
     * between a `Draft` and any other record of the same fields, and it is not in the signature the
     * hint came from.
     */
    public boolean heldToARule(Type type) {
        return type instanceof Type.Ref(TypeSymbol named)
                && symbols.declarations().declaration(named) instanceof Hir.Data data
                && !data.invariants().isEmpty();
    }

    /**
     * What every parameter written in {@code source} is declared to arrive as.
     *
     * <p>A signature is written once, on the {@code behavior} line, and the {@code let} under it
     * repeats none of it — so a reader working in the body has the names and not the types, and the
     * line that says them may be far up the file or in another one. This is not inference shown to
     * an author: it is the declaration they already wrote, carried to where they are working.
     *
     * <p>Answered whether or not the body compiles. What arrives is the signature's to say, and a
     * body that will not check does not stop it saying so.
     */
    public List<DeclaredParameter> parametersIn(SourceId source) {
        Answer<Hir.Module> resolved = db.ask(new Names.Resolved(module));
        Answer<Map<String, Sig>> signatures = db.ask(new Bodies.Signatures(module));
        if (!resolved.present() || !signatures.present()) {
            return List.of();
        }
        List<DeclaredParameter> out = new ArrayList<>();
        for (Hir.FnDef fn : resolved.value().fns()) {
            Sig sig = signatures.value().get(fn.written().canonical());
            if (sig == null || sig.inputTypes().size() != fn.params().size()) {
                continue;
            }
            for (int at = 0; at < fn.params().size(); at++) {
                Hir.Binder binder = fn.params().get(at).binder();
                Type arrives = sig.inputTypes().get(at);
                // A parameter written nowhere is one a pass introduced; there is no name in the
                // source for a hint to stand after.
                if (binder.written().authored() && binder.pos().isIn(source)) {
                    out.add(new DeclaredParameter(binder.written().region(),
                            new TypeFact(arrives, new Evidence.Declared()), heldToARule(arrives)));
                }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The behavior the name written over {@code extent} reaches, and what it declares it takes.
     *
     * <p>Asked of the callee and not of the call. A call is written over everything in it, brackets
     * included, and the last of those may not be typed yet — the name is written before any of that
     * and says which declaration this is about.
     *
     * <p>Empty where the name reaches no behavior: a helper, a local holding a function, a name that
     * resolves to nothing. What those take is not written on a `behavior` line, and there is no
     * declaration here to show.
     */
    public Optional<CalledBehavior> calledAt(Region extent) {
        if (!(sites.written(extent) instanceof Hir.Var.Denoting called)
                || !(called.reachedAs().denotes() instanceof ValueName.Behavior reached)) {
            return Optional.empty();
        }
        Answer<Map<ValueName.Behavior, Sig>> reachable = db.ask(new Bodies.Reachable(module));
        Answer<Hir.Module> declaring = db.ask(new Names.Resolved(reached.module()));
        if (!reachable.present() || !declaring.present()) {
            return Optional.empty();
        }
        Sig sig = reachable.value().get(reached);
        List<Hir.Param> written = parametersOf(declaring.value(), reached.name());
        if (sig == null || written == null || sig.inputTypes().size() != written.size()) {
            // A signature and a declaration that disagree about how many things arrive is a mistake
            // in that module, reported where it is written. Pairing them off anyway would name an
            // argument after a parameter that is not the one arriving there.
            return Optional.empty();
        }
        List<CalledBehavior.Takes> takes = new ArrayList<>();
        for (int at = 0; at < written.size(); at++) {
            takes.add(new CalledBehavior.Takes(written.get(at).name(),
                    new TypeFact(sig.inputTypes().get(at), new Evidence.Declared())));
        }
        return Optional.of(new CalledBehavior(reached.name(), List.copyOf(takes)));
    }

    /** The parameters {@code behavior} is declared with, or null where the module declares no such
     *  behavior or declares it as a composition, which writes none. */
    private static List<Hir.Param> parametersOf(Hir.Module declaring, String behavior) {
        for (Hir.BehaviorDef each : declaring.behaviors()) {
            if (each.written().canonical().equals(behavior)) {
                return each instanceof Hir.SpecBehavior spec ? spec.params() : null;
            }
        }
        return null;
    }

    /**
     * The names a namespace offers, in the order it declares them.
     *
     * <p>What a module publishes and not what it holds: an author writing {@code m.} may write what
     * {@code m} exposes, and offering the rest would be offering names that do not resolve. The
     * module's own {@code exposing} line is that answer, made by the module rather than worked out
     * here from what it happens to declare.
     *
     * <p>Empty for a namespace the language reserves. What is inside one is the standard library's
     * to say, and this reading has not asked it.
     */
    public List<Published> namesIn(MemberReceiver.Namespace namespace) {
        if (!(namespace instanceof MemberReceiver.Namespace.OfModule(String named, Region _))) {
            return List.of();
        }
        Answer<Hir.Module> offering = db.ask(new Names.Resolved(named));
        if (!offering.present()) {
            return List.of();
        }
        Hir.Module offered = offering.value();
        List<Published> out = new ArrayList<>();
        for (String name : offered.exposing()) {
            published(offered, name).ifPresent(out::add);
        }
        return List.copyOf(out);
    }

    /**
     * Which of the things a module declares {@code name} is, or empty where it declares none of
     * them.
     *
     * <p>Empty rather than a fourth kind. A name on an {@code exposing} line that the module does
     * not declare is a mistake in that module, reported where it is written, and offering it here
     * would be offering a name that resolves to nothing.
     */
    private static Optional<Published> published(Hir.Module offered, String name) {
        for (Hir.Def def : offered.defs()) {
            if (def.name().equals(name)) {
                return Optional.of(new Published.AType(name));
            }
        }
        for (Hir.BehaviorDef behavior : offered.behaviors()) {
            if (behavior.written().canonical().equals(name)) {
                return Optional.of(new Published.ABehavior(name));
            }
        }
        for (Hir.FnDef fn : offered.fns()) {
            // A behavior's implementation is declared under the behavior's name and was answered
            // above; what is left here is a definition of the module's own.
            if (fn.written().canonical().equals(name)) {
                return Optional.of(new Published.ADefinition(name));
            }
        }
        return Optional.empty();
    }

    /**
     * The fields a value of {@code held} has, each with what it is declared to be.
     *
     * <p>In the order a declaration lays them out, spreads included, which is the order an author
     * reads them in. Empty for anything that is not a declared data type: a list has no fields to
     * write after a {@code .}, and neither has a type this module cannot see.
     *
     * <p>A newtype has one, and it is the {@code value} it wraps. That is the declaration speaking:
     * a newtype declares one field and what it is is what it was made of.
     */
    public Map<String, Type> fieldsOf(TypeFact held) {
        if (!(held.type() instanceof Type.Ref(TypeSymbol named))) {
            return Map.of();
        }
        if (DeclaredTypeEvidence.isNewtype(named, symbols)) {
            Type wrapped =
                    DeclaredTypeEvidence.shapeOf(DeclaredTypeEvidence.newtypeBaseType(named, symbols));
            return wrapped == null ? Map.of() : Map.of("value", wrapped);
        }
        Map<String, Type> fields = new LinkedHashMap<>();
        DeclaredTypeEvidence.fieldTypes(named, symbols).forEach((field, written) -> {
            Type is = DeclaredTypeEvidence.shapeOf(written);
            if (is != null) {
                fields.put(field, is);
            }
        });
        return fields;
    }

    /**
     * A value receiver, with what the declarations say it is where they say anything.
     *
     * <p>Asked of the one walk that answers what a declaration says about an expression's type, so
     * what an editor is told about {@code request.plannedCost} and what a row's reading is told
     * about it are the same answer. What is added here is the one thing that walk has no way to
     * know on its own: a behavior's parameter is bound by nothing and its type is in the signature
     * above it.
     */
    private MemberReceiver valueReceiver(Hir.Expr receiver) {
        Type declared = declaredTypeOf(receiver);
        return declared == null
                ? new MemberReceiver.UntypedValue(receiver.region())
                : new MemberReceiver.Value(new TypeFact(declared, new Evidence.Declared()),
                        receiver.region());
    }

    /** What the declarations say {@code e} is, or null where they say nothing — including where the
     *  module's signatures or definitions are not answerable, which is one fact being absent rather
     *  than this reading being. */
    private Type declaredTypeOf(Hir.Expr e) {
        Answer<Map<String, Hir.FnDef>> values = db.ask(new Bodies.ModuleDefinitions(module));
        if (!values.present()) {
            return null;
        }
        Map<BindingId, BindingEvidence> parameters = parametersOfEveryBehavior();
        return new DeclaredTypeEvidence(symbols, values.value(), parameters)
                .declaredTypeOf(e, new HashSet<>(), new HashMap<>(parameters));
    }

    /**
     * What every parameter written in this module is declared to arrive as.
     *
     * <p>All of them at once and not the ones the cursor is inside. A binding tells itself from
     * every other, so a parameter of one behavior cannot be reached by a name in another, and
     * working out which body a position is in would be a scope this does not have to keep.
     *
     * <p>A behavior whose signature says a different number of things from what its {@code let}
     * writes is left out. The two disagreeing is a mistake in the module, reported where it is
     * written, and pairing them off by position anyway would say a parameter arrives as something
     * the declaration never said it does.
     */
    private Map<BindingId, BindingEvidence> parametersOfEveryBehavior() {
        Answer<Hir.Module> resolved = db.ask(new Names.Resolved(module));
        Answer<Map<String, Sig>> signatures = db.ask(new Bodies.Signatures(module));
        if (!resolved.present() || !signatures.present()) {
            return Map.of();
        }
        Map<BindingId, BindingEvidence> declared = new LinkedHashMap<>();
        for (Hir.FnDef fn : resolved.value().fns()) {
            Sig sig = signatures.value().get(fn.written().canonical());
            if (sig == null) {
                continue;
            }
            List<Type> arrives = sig.inputTypes();
            if (arrives.size() != fn.params().size()) {
                continue;
            }
            for (int at = 0; at < arrives.size(); at++) {
                declared.put(fn.params().get(at).binder().id(),
                        new BindingEvidence.DeclaredAs(arrives.get(at)));
            }
        }
        return declared;
    }

    /**
     * The namespace a qualified name is reached through, or empty where the name is not qualified or
     * its qualifier names none.
     *
     * <p>Answered to the module rather than to the spelling. An import may bring a module in under
     * any name it likes, so what {@code m} is is a question about this module's imports, and a
     * reader handed the spelling would have to ask it again.
     */
    private Optional<MemberReceiver> namespaceOf(WrittenName name) {
        String written = name.canonical();
        int lastDot = written.lastIndexOf('.');
        if (lastDot < 0 || name.segments().size() < 2) {
            return Optional.empty();
        }
        String qualifier = written.substring(0, lastDot);
        // Every segment but the last, which is what the qualifier is written over. Taken from the
        // occurrences the name carries rather than measured in the spelling: the two differ by
        // whatever the grammar lets stand between a qualifier and the name it qualifies.
        Region at = new Region(name.segments().getFirst().start(),
                name.segments().get(name.segments().size() - 2).end());
        String namespace = symbols.scope().moduleOfQualifier(qualifier);
        if (namespace != null) {
            return Optional.of(new MemberReceiver.Namespace.OfModule(namespace, at));
        }
        return Reserved.isQualifier(qualifier)
                ? Optional.of(new MemberReceiver.Namespace.OfLibrary(qualifier, at))
                : Optional.empty();
    }
}
