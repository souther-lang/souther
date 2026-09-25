package souther.compiler.query;

import souther.compiler.Reserved;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorBodies;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Derived;
import souther.compiler.check.Preserved;
import souther.compiler.check.Requirements;
import souther.compiler.check.Sig;
import souther.compiler.check.ValueEntries;
import souther.compiler.check.DerivedSymbols;
import souther.compiler.codegen.LinkageProjections;
import souther.compiler.codegen.LinkageReader;
import souther.compiler.core.CompleteSignature;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.jvm.LinkageProjection;
import souther.compiler.jvm.LinkageRecord;
import souther.compiler.jvm.LinkageTarget;
import souther.compiler.meta.LinkageAgreement;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.SortedMap;
import java.util.TreeMap;
import java.util.function.Function;

/**
 * What each module's declarations offer another module's classes on the JVM, and whether a module
 * read off the path links against what the modules this compilation has offer.
 *
 * <p>A compiled module carries both halves of this: what its declarations provide, and what each
 * declaration of another module its classes read offered when they read it. A module read off the
 * path is held to the second half against the first half of the modules it names — theirs as they
 * are recorded, for a module off the path, and as they are about to be emitted, for one compiled
 * here. Nothing is worked out again for the module being held: what it provides is what its classes
 * offer, and what it would provide if built again is another module.
 */
public final class Linkages {

    private Linkages() {}

    /**
     * What a module's declarations offer, and what of other modules' declarations was read to
     * work that out.
     *
     * @param provides what each declaration offers, by the declaration
     * @param read     each declaration of another module read while those projections were made,
     *                 and what it offered — part of what the module is built against
     */
    public record Of(Map<LinkageTarget, LinkageProjection> provides,
                     Map<LinkageTarget, LinkageProjection> read) {
        public Of {
            provides = Collections.unmodifiableMap(new TreeMap<>(provides));
            read = Collections.unmodifiableMap(new TreeMap<>(read));
        }
    }

    /**
     * Every module whose declarations a module may be built against: every module it names —
     * imported, or written as a qualifier, which needs no import — what the modules it reads off the
     * path carry beside their text as reaching, and so on from each.
     *
     * <p>A behavior a composition builds may be declared in a module the composition's own module
     * never imports — the stage's module does — so what a projection or an emission reads is bounded
     * by this and not by the import lines of the one module. The language's own modules are not
     * here: what they declare is the same on every side of every artifact.
     */
    public record InSight(String name) implements Key<List<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<String>> compute(Db db) {
            Set<String> seen = new LinkedHashSet<>();
            Deque<String> pending = new ArrayDeque<>();
            pending.add(name);
            while (!pending.isEmpty()) {
                String module = pending.removeFirst();
                if (Reserved.isNamespace(module) || !seen.add(module)) {
                    continue;
                }
                List<String> named = db.ask(new Named(module)).value();
                if (named != null) {
                    pending.addAll(named);
                }
            }
            return Answer.of(List.copyOf(seen));
        }
    }

    /**
     * The modules one module names: what it imports or writes as a qualifier, and, for a module
     * off the path, what it carries beside its text as reaching.
     *
     * <p>Its own question so a module's text is walked for these once, whichever module's
     * {@link InSight} it is on the way to.
     */
    public record Named(String name) implements Key<List<String>> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<List<String>> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null) {
                return Answer.of(List.copyOf(Front.reaches(onThePath.read())));
            }
            Ast.Module written = db.ask(new Front.Available(name)).value();
            return written == null ? Answer.of(List.of())
                    : Answer.of(List.copyOf(Front.reaches(written).keySet()));
        }
    }

    /**
     * Whether every module {@code name} may be built against, other than itself, has something to
     * offer here — which a module that did not come out, or one off the path held to another version
     * of what it was built against, does not.
     *
     * <p>Asked of whether each offers anything and not of what it offers, so a module is told when
     * one of those stops or starts coming out and not whenever one of them declares something.
     * What each declaration offers is asked one declaration at a time where it is read
     * ({@link #reading}).
     */
    static boolean everyModuleInSightOffers(Db db, String name) {
        List<String> inSight = db.ask(new InSight(name)).value();
        if (inSight == null) {
            return false;
        }
        for (String module : inSight) {
            if (!module.equals(name) && held(db, module)
                    && !db.ask(new Offers(module)).present()) {
                return false;
            }
        }
        return true;
    }

    /**
     * What another module's declaration offers, asked of this compilation one declaration at a time
     * — or null where nothing here provides it.
     */
    static Function<LinkageTarget, LinkageProjection> reading(Db db) {
        return target -> db.ask(new Projection(target)).value();
    }

    /** That a module has something to offer here ({@link Provided}), and nothing about what. */
    public record Offers(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            return db.ask(new Provided(name)).present() ? Answer.of(Boolean.TRUE) : Answer.absent();
        }
    }

    /**
     * What one declaration offers another module's classes, as the module that declares it provides
     * it here.
     *
     * <p>Its own question so that a class built against a declaration is built against that one: a
     * module's classes read the declarations they read, and what else the module declares, or
     * comes to declare, is not theirs to be told about.
     */
    public record Projection(LinkageTarget target) implements Key<LinkageProjection> {
        @Override
        public String module() {
            return target.module();
        }

        @Override
        public Answer<LinkageProjection> compute(Db db) {
            if (!held(db, target.module())) {
                return Answer.absent();
            }
            Answer<Of> provided = db.ask(new Provided(target.module()));
            if (!provided.present()) {
                return Answer.absent();
            }
            LinkageProjection found = provided.value().provides().get(target);
            return found == null ? Answer.absent() : Answer.of(found);
        }
    }

    /** Whether this compilation has {@code module}, compiled here or on the path. */
    private static boolean held(Db db, String module) {
        return Front.onThePath(db, module) != null
                || (db.ask(new Front.Declared()).value() instanceof List<String> declared
                        && declared.contains(module));
    }

    /**
     * What a module's declarations offer another module's classes ({@link LinkageProjections}).
     *
     * <p>For a module compiled here, what its classes are about to offer: made out of what its
     * declarations settled, reading what the modules it is built against offer for what rests on
     * them.
     *
     * <p>For a module read off the path, made the same way out of what it published — and asked
     * only once the module has been held to what it was built against ({@link Held}), since its
     * classes are what the module offers and a module whose classes were built against something
     * else offers what they offer, not what this would work out. Held, the two are the same, and
     * that is checked: a difference is this compiler making a projection two ways.
     */
    public record Provided(String name) implements Key<Of> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Of> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath != null && !db.ask(new Held(name)).present()) {
                return Answer.absent();
            }
            if (!everyModuleInSightOffers(db, name)) {
                return Answer.absent();
            }
            LinkageReader reader = new LinkageReader(name, reading(db));
            Ast.Module written = db.ask(new Front.Available(name)).value();
            Answer<Map<String, Sig>> signatures = db.ask(new Bodies.Signatures(name));
            Answer<BehaviorBodies> implementations = db.ask(new Bodies.Implementation(name));
            Answer<Map<String, List<BehaviorRequirement>>> requirements =
                    db.ask(new Bodies.Requirements(name));
            Answer<DerivedSymbols> symbols = Names.derivedSymbols(db, name, reader);
            Map<String, Type> values = publishedValues(db, name, onThePath);
            if (written == null || !signatures.present() || !implementations.present()
                    || !requirements.present() || !symbols.present() || values == null) {
                return Answer.absent();
            }
            List<TypeKey> declarations = new ArrayList<>();
            for (Ast.Def def : written.defs()) {
                TypeKey declaration = def.declaredKey();
                // A product whose boundary representation did not come out is said where it is
                // written; how it is decoded is part of what it offers, so there is nothing to offer.
                if (symbols.value().declaredNode(declaration) instanceof Hir.Data
                        && !(symbols.value().declarations().declaration(declaration)
                                instanceof Derived.Data)) {
                    return Answer.absent();
                }
                declarations.add(declaration);
            }
            Map<String, List<ValueName.Behavior>> required = new LinkedHashMap<>();
            requirements.value().forEach((behavior, each) ->
                    required.put(behavior, Requirements.names(each)));
            SortedMap<LinkageTarget, LinkageProjection> provides = LinkageProjections.of(
                    new LinkageProjections.Settled(name, written.published(), declarations,
                            signatures.value(), implementations.value().states(), required,
                            values, symbols.value(),
                            reader.readingPublished(Shapes.publishedDeclarations(db))),
                    reader);
            if (onThePath != null) {
                itOffersWhatItsClassesOffer(name, provides, onThePath.provides());
            }
            return Answer.of(new Of(provides, reader.read()));
        }
    }

    /**
     * What each value {@code name} publishes answers, by the value, as the module's own check
     * settled it — or null where that check has no answer.
     *
     * <p>A module off the path records exactly the values it publishes; one compiled here settles
     * every value it declares, and what it publishes is asked of its declarations.
     */
    private static Map<String, Type> publishedValues(Db db, String name,
                                                     Front.FromPath.OnThePath onThePath) {
        Map<String, Type> out = new LinkedHashMap<>();
        if (onThePath != null) {
            onThePath.valueAnswers().signatures().forEach((value, signature) -> {
                if (value instanceof ValueName.Helper helper && helper.module().equals(name)) {
                    out.put(helper.name(), signature.result());
                }
            });
            return out;
        }
        Answer<Bodies.ModuleCheck.Of> checked = db.ask(new Bodies.ModuleCheck(name));
        Answer<Hir.Module> settled = db.ask(new Bodies.Settled(name));
        if (!checked.present() || !settled.present()) {
            return null;
        }
        Preserved.SettledValues answered = checked.value().settledValues();
        for (String value : ValueEntries.publishedValues(settled.value())) {
            CompleteSignature signature =
                    answered.signatures().get(new ValueName.Helper(name, value));
            if (signature == null) {
                throw new IllegalStateException("`" + name + "." + value + "` is published and"
                        + " was settled as nothing");
            }
            out.put(value, signature.result());
        }
        return out;
    }

    /**
     * That what this compiler works out a module off the path provides is what its classes record
     * they offer.
     *
     * <p>Asked of a module already held to what it was built against, and so one whose own
     * declarations and whatever of other modules they rest on are what they were when it was built.
     * Worked out from those by the rules its classes were emitted by, a projection is what it was;
     * one that is not is two ways of making a projection in this compiler, and not a fact about the
     * artifact.
     */
    private static void itOffersWhatItsClassesOffer(
            String name, Map<LinkageTarget, LinkageProjection> workedOut,
            Map<LinkageTarget, LinkageRecord> recorded) {
        Map<LinkageTarget, LinkageRecord> asRecorded = new TreeMap<>();
        workedOut.forEach((target, projection) ->
                asRecorded.put(target, LinkageRecord.of(projection)));
        if (!asRecorded.equals(recorded)) {
            List<String> differing = new ArrayList<>();
            Set<LinkageTarget> targets = new LinkedHashSet<>(recorded.keySet());
            targets.addAll(asRecorded.keySet());
            for (LinkageTarget target : targets) {
                LinkageRecord was = recorded.get(target);
                LinkageRecord now = asRecorded.get(target);
                if (was == null || now == null) {
                    differing.add(target.shown() + (was == null ? " is not recorded"
                            : " is recorded and not worked out"));
                } else if (!was.equals(now)) {
                    differing.add(target.shown() + ": " + was.movedIn(now));
                }
            }
            throw new IllegalStateException("what " + name + " provides was worked out otherwise"
                    + " than its classes record it: " + differing);
        }
    }

    /**
     * Whether a module read off the path links against what this compilation has: each declaration
     * of another module its classes were built against, held to what that declaration's module
     * offers here (spec {@code [#a-published-module-agrees-with-what-it-was-built-against]}).
     *
     * <p>What a module compiled here offers is what its classes are about to offer; what a module
     * off the path offers is what its classes record. A declaration a module off the path offers
     * differently from what a module built against it assumed is said about the module that assumed
     * it — the one whose classes stop when they reach it — and not about any module built on that
     * one: a module that did not read the declaration is not held to it.
     *
     * <p>Asked of every module read off the path, where the compilation's problems are gathered, and
     * not by whoever goes on to use some of the module.
     *
     * <p>A module compiled here is built against what it is compiled with, and agrees.
     */
    public record Held(String name) implements Key<Boolean> {
        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Front.FromPath.OnThePath onThePath = Front.onThePath(db, name);
            if (onThePath == null) {
                return Answer.of(Boolean.TRUE);
            }
            // A module whose own declarations name what is no longer there is said where its names
            // are read, and a declaration its classes link against being gone is that same thing
            // said again; it is not held here until its names are.
            if (!Boolean.TRUE.equals(db.ask(new Names.Sound(name)).value())) {
                return Answer.absent();
            }
            // What each module offers, worked out once for all the declarations of it required.
            Map<String, Map<LinkageTarget, LinkageRecord>> offeredBy = new HashMap<>();
            LinkageAgreement.Held held = LinkageAgreement.of(onThePath.requires(),
                    module -> offeredBy.computeIfAbsent(module, m -> offered(db, m)));
            // A behavior the module was built requiring injected that its module no longer declares
            // is said as that (Bodies.BuiltAgainst); its classes linking against it is the
            // same missing behavior, and one problem is said once.
            Set<LinkageTarget> requiredInjected = new LinkedHashSet<>();
            for (List<ValueName.Behavior> each : onThePath.behaviorRequirements().values()) {
                for (ValueName.Behavior dependency : each) {
                    requiredInjected.add(new LinkageTarget.Behavior(dependency));
                }
            }
            List<Report> reports = new ArrayList<>();
            boolean saidElsewhere = false;
            for (LinkageAgreement.Disagreement disagreement : held.disagreements()) {
                LinkageTarget target = disagreement.target();
                if (disagreement instanceof LinkageAgreement.Disagreement.NotProvided
                        && requiredInjected.contains(target)) {
                    saidElsewhere = true;
                    continue;
                }
                Diagnostic said = switch (disagreement) {
                    case LinkageAgreement.Disagreement.NotProvided _ ->
                            Bodies.BuiltAgainst.builtAgainstAnother(
                                    new ModuleMessage.ItLinksAgainstWhatTheModuleDoesNotProvide(
                                            name, target.kind(), target.name(), target.module()),
                                    name, target.module());
                    case LinkageAgreement.Disagreement.Moved moved -> {
                        LinkageRecord.Moved first = moved.moved().getFirst();
                        yield Bodies.BuiltAgainst.builtAgainstAnother(
                                new ModuleMessage.ItWasBuiltAgainstAnotherLinkage(name,
                                        target.kind(), target.name(), target.module(),
                                        first.label(), shown(first.was()), shown(first.now())),
                                name, target.module());
                    }
                };
                reports.add(Report.raised(said));
            }
            if (!reports.isEmpty()) {
                return Answer.absent(reports);
            }
            // A module not in this compilation, or one that did not come out, or a behavior said
            // missing as a requirement: said where it is found, and not held here.
            return held.complete() && !saidElsewhere ? Answer.of(Boolean.TRUE) : Answer.absent();
        }
    }

    /**
     * What {@code module} offers as a class built against it reads it: as its classes record it,
     * for a module off the path, and as its classes are about to offer it, for one compiled here —
     * or null where this compilation does not have it, or it did not come out.
     */
    private static Map<LinkageTarget, LinkageRecord> offered(Db db, String module) {
        Front.FromPath.OnThePath onThePath = Front.onThePath(db, module);
        if (onThePath != null) {
            return onThePath.provides();
        }
        if (!held(db, module)) {
            return null;
        }
        Answer<Of> provided = db.ask(new Provided(module));
        if (!provided.present()) {
            return null;
        }
        Map<LinkageTarget, LinkageRecord> out = new TreeMap<>();
        provided.value().provides().forEach((target, projection) ->
                out.put(target, LinkageRecord.of(projection)));
        return out;
    }

    /** One side of a fact that moved, as a report shows it; a dash where that side says nothing. */
    private static String shown(String fact) {
        return fact == null ? "—" : fact;
    }
}
