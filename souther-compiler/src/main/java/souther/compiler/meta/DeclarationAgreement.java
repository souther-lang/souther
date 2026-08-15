package souther.compiler.meta;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.Prelude;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.lang.reflect.RecordComponent;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

/**
 * Holds the declarations an answer reads a row's values by against the declarations the row is
 * written for.
 *
 * <p>Both sides go through {@link PublishedModule#read}, which is the one projection there is from
 * classes to declarations: what a module publishes is decided where it is stamped, read back by the
 * front end that read it in the first place, and this compares what comes out. A comparison that
 * read the annotations itself would be a second statement of what a module publishes, and the two
 * would have to be kept saying the same thing by hand.
 *
 * <p>What it answers is not whether the two are the same build. Builds differ in ways a crossing
 * cannot see, and a check that reported those would report a model as one whose rows do not hold
 * every time anything at all was edited. What is compared is what a crossing depends on: which cases
 * a union has, what a data holds, what an invariant admits, what a newtype wraps, what a behavior's
 * signature is, and the helpers an invariant is not readable without. A {@code let} body, an example,
 * where a declaration was written, how it was spaced — none of it is read.
 *
 * <p>The comparison is over declarations and not over their text. Text differs where nothing does:
 * a declaration reformatted says the same thing, and reporting that as a stale build would be
 * reporting a difference a crossing cannot see. So both sides are parsed and their declarations
 * compared as the forms they are, with where each was written left out of it.
 *
 * <p>It follows imports. A field of an imported type is read by that module's declarations, so a
 * module whose own declarations agree can still be read by an invariant from a build that has moved.
 * An import is the edge here rather than the thing compared — what is compared is the module it
 * reaches, on both sides, by the same rule.
 */
public final class DeclarationAgreement {

    private DeclarationAgreement() {}

    /**
     * Whether {@code theirs} declares {@code module}, and everything its declarations reach, as
     * {@code ours} does.
     *
     * @param module the module being evaluated, which is where the walk starts
     * @param ours   where the declarations the rows are written for are read from
     * @param theirs where the declarations the answer reads values by are read from
     */
    public static Agreement of(String module, PublishedModule.Classes ours,
                               PublishedModule.Classes theirs) {
        Deque<String> toRead = new ArrayDeque<>(List.of(module));
        Set<String> read = new LinkedHashSet<>(List.of(module));
        while (!toRead.isEmpty()) {
            String name = toRead.removeFirst();
            Reading mine = reading(name, ours);
            Reading yours = reading(name, theirs);
            if (mine.why() != null) {
                return new Agreement.Unreadable(name, mine.why(),
                        Agreement.Side.THE_MODULE_BEING_EVALUATED);
            }
            if (yours.why() != null) {
                return new Agreement.Unreadable(name, yours.why(), Agreement.Side.THE_ANSWER);
            }
            Agreement said = agreed(name, mine.published(), yours.published());
            if (!(said instanceof Agreement.Agree)) {
                return said;
            }
            // What is followed is the modules the compared declarations reach into, of the module as
            // it is being evaluated: what the rows are written for is what a value crossing has to be
            // readable by. Not the import lines — a module may import what only an unread helper
            // wanted, and may reach a declaration written out in full with no import at all, so the
            // lines and the modules a crossing depends on are two different sets.
            //
            // The standard library is in neither: nobody publishes it, and whether two builds have
            // the same one is what the boundary revision on each of them says.
            for (String reached : modulesReached(mine.published().module())) {
                if (read.add(reached)) {
                    toRead.addLast(reached);
                }
            }
        }
        return new Agreement.Agree();
    }

    /**
     * What the names written in one module mean: which declaration each of them reaches.
     *
     * <p>A declaration is compared by what it says, and what a name says is which declaration it
     * names — not how it was spelled to get there. The language settles a bare name brought in by an
     * import, a name written under an alias, and one written out in full to the same declaration
     * (spec {@code modules}), so all three read alike here.
     *
     * <p>What this is not is the compiler's resolution. It is the part of it a published declaration
     * carries with it: the import lines are on the module, and a qualified name says its module in
     * itself. That is enough to say which declaration a name reaches, which is the whole of what a
     * crossing depends on about one.
     *
     * @param moduleOfImportedName which module a bare name was brought in from
     * @param moduleOfAlias        which module a qualifier stands for
     */
    private record Names(Map<String, String> moduleOfImportedName, Map<String, String> moduleOfAlias) {

        static Names of(Ast.Module module) {
            Map<String, String> byName = new LinkedHashMap<>();
            Map<String, String> byAlias = new LinkedHashMap<>();
            for (Ast.Import imported : module.imports()) {
                for (Ast.ImportedName name : imported.importedNames()) {
                    byName.put(name.written().canonical(), imported.module());
                }
                if (imported.alias() != null) {
                    byAlias.put(imported.alias(), imported.module());
                }
            }
            return new Names(byName, byAlias);
        }

        /**
         * {@code written} as which declaration it reaches: the module that declares it and the name
         * it is declared under.
         *
         * <p>A name this module declares itself, and a standard-library one, are left as they are —
         * the first is the same on both sides by being the same module's, and the second is what a
         * compiler has rather than what a build published.
         */
        String reaching(String written) {
            int dot = written.lastIndexOf('.');
            if (dot < 0) {
                String from = moduleOfImportedName.get(written);
                return from == null ? written : from + "." + written;
            }
            String qualifier = written.substring(0, dot);
            String from = moduleOfAlias.get(qualifier);
            return from == null ? written : from + written.substring(dot);
        }

        /** The module a name reaches into, where it reaches out of this one at all. */
        String moduleReached(String written) {
            String reaching = reaching(written);
            int dot = reaching.lastIndexOf('.');
            if (dot < 0) {
                return null;
            }
            String qualifier = reaching.substring(0, dot);
            return Prelude.isQualifier(qualifier) ? null : qualifier;
        }
    }

    /** A module's published declarations, or why they could not be read. Exactly one is set. */
    private record Reading(PublishedModule published, Agreement.Reason why) {}

    /**
     * {@code module}'s published declarations, or the reason there are none to compare.
     *
     * <p>{@link PublishedModule#read} raises where the declarations are there and this compiler does
     * not read them, which is a compile failing when a module is being imported. Here it is one of
     * the things being asked about, so it is answered rather than raised — a run that let it out
     * would stop evaluating a module because one behavior's answer brought classes it could not read.
     *
     * <p>Every way of raising is the answer rather than a failure, which is why what is caught is
     * as wide as it is. This compiler declining what a class says is one (a compile exception);
     * the class file not being one this JVM reads is another — truncated bytes, a major version from
     * a newer JDK, which the class-file reader raises as it sees fit. An answer brings its classes
     * from wherever it was built, so both are ordinary things to meet here, and both mean the same:
     * nothing about the two could be established.
     */
    private static Reading reading(String module, PublishedModule.Classes classes) {
        try {
            PublishedModule published = PublishedModule.read(module, classes);
            return published == null
                    ? new Reading(null, Agreement.Reason.NOTHING_PUBLISHED)
                    : new Reading(published, null);
        } catch (RuntimeException _) {
            return new Reading(null, Agreement.Reason.NOT_READABLE_HERE);
        }
    }

    /** Whether two readings of one module say the same thing about what a crossing depends on. */
    private static Agreement agreed(String module, PublishedModule ours, PublishedModule theirs) {
        Names mine = Names.of(ours.module());
        Names yours = Names.of(theirs.module());
        Agreement types = held(module, byName(ours.module().defs(), Ast.Def::name),
                byName(theirs.module().defs(), Ast.Def::name), DeclarationAgreement::crossingParts,
                mine, yours);
        if (!(types instanceof Agreement.Agree)) {
            return types;
        }
        Agreement behaviors = held(module,
                byName(ours.module().behaviors(), Ast.BehaviorDef::name),
                byName(theirs.module().behaviors(), Ast.BehaviorDef::name),
                DeclarationAgreement::crossingParts, mine, yours);
        if (!(behaviors instanceof Agreement.Agree)) {
            return behaviors;
        }
        // A module publishes more `let`s than a declaration is read through: what it exposes travels
        // too, because a reader substitutes a value where it is named and expands a helper where it
        // is called. Those are read by whatever calls them, and a row's values crossing into an
        // answer never do — what they meet is what a declaration says, so what is compared is the
        // helpers a declaration cannot be read without.
        Set<String> readThrough = readThrough(ours.module());
        Agreement helpers = held(module,
                byName(publishedHelpers(ours.module(), readThrough), fn -> fn.written().canonical()),
                byName(publishedHelpers(theirs.module(), readThrough), fn -> fn.written().canonical()),
                DeclarationAgreement::crossingParts, mine, yours);
        if (!(helpers instanceof Agreement.Agree)) {
            return helpers;
        }
        // Which behaviors are left to be injected does not survive as source, so it is carried beside
        // the module. It decides whether an implementation may be supplied for a behavior at all,
        // which is as much a fact about the crossing as the behavior's signature is.
        if (!ours.injectedBehaviors().equals(theirs.injectedBehaviors())) {
            return new Agreement.Disagree(module, first(difference(ours.injectedBehaviors(),
                    theirs.injectedBehaviors())));
        }
        return new Agreement.Agree();
    }

    /**
     * The declarations of one kind held against each other, by name.
     *
     * <p>A name only one side has is a difference in itself: a case added to a union, a type that was
     * removed. It is named as the declaration that differs, which is what it is.
     */
    private static <T> Agreement held(String module, Map<String, T> ours, Map<String, T> theirs,
                                      java.util.function.Function<T, List<Object>> parts,
                                      Names mine, Names yours) {
        for (Map.Entry<String, T> ourOwn : ours.entrySet()) {
            T theirOwn = theirs.get(ourOwn.getKey());
            if (theirOwn == null
                    || !sameShape(parts.apply(ourOwn.getValue()), parts.apply(theirOwn), mine, yours)) {
                return new Agreement.Disagree(module, ourOwn.getKey());
            }
        }
        for (String name : theirs.keySet()) {
            if (!ours.containsKey(name)) {
                return new Agreement.Disagree(module, name);
            }
        }
        return new Agreement.Agree();
    }

    /**
     * What a value crossing into a data declaration depends on.
     *
     * <p>Stated as a switch over the declarations there are, so a kind of declaration added later is
     * a compile error here rather than one silently compared by nothing. What the error asks for is a
     * classification: either the new form bears on how a value crosses and its parts belong here, or
     * it cannot and is left out on purpose.
     *
     * <p>Where a declaration is written is not among them. Two builds of one model write their
     * declarations in a file each, and a line number is not something a value crossing can be read
     * differently by.
     */
    private static List<Object> crossingParts(Ast.Def def) {
        return switch (def) {
            // Everything a product is: whether it is a newtype (which is what it is represented as),
            // what it includes and holds, what it admits, and how it is read and written.
            case Ast.Data d -> List.of(d.newtype(), d.includes(), d.fields(), d.invariants(),
                    d.decoder(), d.encoder());
            // Which cases a union has, and how one is told from another.
            case Ast.SumData s -> List.of(s.cases(), s.decoder(), s.encoder());
            // A unit is its name, which is what it was looked up by.
            case Ast.UnitData _ -> List.of();
        };
    }

    /** What a value crossing into a behavior depends on: what it takes and what it answers with. */
    private static List<Object> crossingParts(Ast.BehaviorDef behavior) {
        return switch (behavior) {
            case Ast.SpecBehavior b -> List.of(b.params(), b.ret(), b.constructs(), b.dependsOn());
            // A composition does not arrive here. What a module publishes for one is the signature
            // its stages compute (`ModuleMetadata.signatureOf`), so what comes back from a jar is a
            // declared behavior like any other, and its stages are the module's own business. Said
            // as a refusal rather than as a comparison of the stages, because a comparison written
            // for a form that never arrives is a rule nobody can read the truth of.
            case Ast.PipeBehavior p -> throw new IllegalStateException(
                    "`" + p.name() + "` is published as the signature its stages compute, so a"
                            + " composition is not a form a published declaration is read back as");
        };
    }

    /**
     * A published helper, whole.
     *
     * <p>These are carried because a declaration cannot be read without them — an invariant calls
     * them, a published value is substituted where it is named — so a helper that computes something
     * else makes the declaration carrying it admit something else. There is no part of one that a
     * crossing does not depend on.
     */
    private static List<Object> crossingParts(Ast.FnDef fn) {
        return List.of(fn.params(), fn.declaredReturn() == null ? "" : fn.declaredReturn(),
                fn.body(), fn.modifiers());
    }

    /**
     * The helpers a declaration of {@code module} cannot be read without.
     *
     * <p>Reached by the same walk that decided what to publish, rather than by a second reading of
     * the same question. A helper this misses is one a declaration is compared without the thing
     * that says what it admits.
     */
    private static Set<String> readThrough(Ast.Module module) {
        Map<String, Ast.FnDef> own = byName(module.fns(), fn -> fn.written().canonical());
        Set<String> reached = new LinkedHashSet<>();
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data data) {
                for (Ast.InvariantClause clause : data.invariants()) {
                    ModuleMetadata.reach(clause.expr(), own, reached);
                }
            }
        }
        return reached;
    }

    /** Everything of {@code module} this comparison reads: its declarations, its behaviors'
     *  signatures, and the helpers a declaration cannot be read without. */
    private static List<Object> compared(Ast.Module module, Set<String> readThrough) {
        List<Object> forms = new ArrayList<>(module.defs());
        forms.addAll(module.behaviors());
        forms.addAll(publishedHelpers(module, readThrough));
        return forms;
    }

    /** The published helpers of {@code module} that are among {@code readThrough}. */
    private static List<Ast.FnDef> publishedHelpers(Ast.Module module, Set<String> readThrough) {
        List<Ast.FnDef> kept = new ArrayList<>();
        for (Ast.FnDef fn : module.fns()) {
            if (readThrough.contains(fn.written().canonical())) {
                kept.add(fn);
            }
        }
        return kept;
    }

    /**
     * The modules the declarations of {@code module} reach into.
     *
     * <p>From the names those declarations are written with, read as the declarations they reach
     * ({@link Names}). That is the same projection the comparison itself is over, so what is followed
     * and what is compared cannot come apart: a module reached is one some compared declaration
     * names, and a module named by nothing compared is not followed however it was imported.
     */
    private static Set<String> modulesReached(Ast.Module module) {
        Names names = Names.of(module);
        Set<String> reached = new LinkedHashSet<>();
        for (String written : namesWritten(compared(module, readThrough(module)))) {
            String from = names.moduleReached(written);
            if (from != null && !from.equals(module.name())) {
                reached.add(from);
            }
        }
        return reached;
    }

    /**
     * Every name written in the declarations compared.
     *
     * <p>Names, and not every word a form holds as text. What a clause is called, what a tag is
     * spelled, what a literal says — none of them is a name a declaration is read through, and
     * reading one as a name makes a module look reached that nothing reaches.
     */
    private static Set<String> namesWritten(List<?> forms) {
        Set<String> written = new LinkedHashSet<>();
        for (Object form : forms) {
            collectNames(form, written, new java.util.IdentityHashMap<>());
        }
        return written;
    }

    private static void collectNames(Object form, Set<String> into, Map<Object, Boolean> seen) {
        if (form == null || ERASED.contains(form.getClass()) || seen.put(form, Boolean.TRUE) != null) {
            return;
        }
        if (form instanceof WrittenName name) {
            into.add(name.canonical());
            return;
        }
        if (form instanceof Optional<?> maybe) {
            collectNames(maybe.orElse(null), into, seen);
            return;
        }
        if (form instanceof Iterable<?> many) {
            for (Object one : many) {
                collectNames(one, into, seen);
            }
            return;
        }
        if (form instanceof Map<?, ?> byKey) {
            for (Map.Entry<?, ?> entry : byKey.entrySet()) {
                collectNames(entry.getKey(), into, seen);
                collectNames(entry.getValue(), into, seen);
            }
            return;
        }
        if (!form.getClass().isRecord()) {
            return;
        }
        for (RecordComponent part : form.getClass().getRecordComponents()) {
            collectNames(read(part, form), into, seen);
        }
    }

    /**
     * Whether two written forms are the same form.
     *
     * <p>Over the forms themselves rather than a walk naming each kind of node. Every part of a
     * declaration that is not where it was written bears on what it means — an operand of an
     * invariant, a field's type, a helper's body — so there is one rule here and not a classification
     * per kind of expression: everything is compared, and where a thing was written is not.
     *
     * <p>What is left out is exactly that. A position and a region are where something is in a file,
     * and a name is compared by what it is rather than by how it was spelled, because a spelling that
     * canonicalises to the same name is the same name to everything that resolves one.
     */
    private static boolean sameShape(Object ours, Object theirs, Names ourNames, Names theirNames) {
        if (ours == null || theirs == null) {
            return ours == theirs;
        }
        if (ERASED.contains(ours.getClass())) {
            return ERASED.contains(theirs.getClass());
        }
        if (ours instanceof WrittenName ourName && theirs instanceof WrittenName theirName) {
            // Which declaration each name reaches, rather than the spelling that reached it.
            return ourNames.reaching(ourName.canonical())
                    .equals(theirNames.reaching(theirName.canonical()));
        }
        if (ours instanceof Optional<?> mine && theirs instanceof Optional<?> yours) {
            return sameShape(mine.orElse(null), yours.orElse(null), ourNames, theirNames);
        }
        if (ours instanceof List<?> mine && theirs instanceof List<?> yours) {
            if (mine.size() != yours.size()) {
                return false;
            }
            for (int i = 0; i < mine.size(); i++) {
                if (!sameShape(mine.get(i), yours.get(i), ourNames, theirNames)) {
                    return false;
                }
            }
            return true;
        }
        if (ours instanceof Set<?> mine && theirs instanceof Set<?> yours) {
            // What an import brings in, and anything else whose members are the whole of it. Its
            // members are values — a set of forms would need each matched to one of the others,
            // which is a different comparison than this and is not one anything here asks for.
            for (Object member : mine) {
                if (member != null && !comparedAsAValue(member.getClass())) {
                    throw new IllegalStateException(unclassified(member.getClass()));
                }
            }
            return mine.equals(yours);
        }
        if (ours instanceof Map<?, ?> mine && theirs instanceof Map<?, ?> yours) {
            return mine.keySet().equals(yours.keySet())
                    && mine.entrySet().stream()
                            .allMatch(e -> sameShape(e.getValue(), yours.get(e.getKey()),
                                    ourNames, theirNames));
        }
        if (ours.getClass() != theirs.getClass()) {
            return false;
        }
        if (!ours.getClass().isRecord()) {
            if (!comparedAsAValue(ours.getClass())) {
                throw new IllegalStateException(unclassified(ours.getClass()));
            }
            // A number is compared by amount. Java's equality for one takes the scale it was written
            // with into account, and the language does not: two invariants stating `1.0m` and
            // `1.00m` admit the same values, and reporting that as a build that has moved would be
            // this comparison deciding something the language denies.
            if (ours instanceof java.math.BigDecimal mine
                    && theirs instanceof java.math.BigDecimal yours) {
                return mine.compareTo(yours) == 0;
            }
            return ours.equals(theirs);
        }
        // Everything else a declaration is made of is a form of the grammar, and a form of the
        // grammar is compared part by part. That is the safe default of the two: a form added to the
        // language and compared when it need not have been reports a build that has not moved, which
        // is a diagnostic someone reads and answers by erasing it here — where a form left out
        // reports agreement that was never established, and nobody ever finds out.
        //
        // A record from outside the grammar is not one of those, and is where the decision has to be
        // made rather than defaulted: what arrives that way carries how something was resolved or
        // where it came from, and neither is what a declaration says.
        if (!isAFormOfTheGrammar(ours.getClass())) {
            throw new IllegalStateException(unclassified(ours.getClass()));
        }
        for (RecordComponent part : ours.getClass().getRecordComponents()) {
            if (!sameShape(read(part, ours), read(part, theirs), ourNames, theirNames)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Where something is written, which two builds of one declaration differ in for no reason a
     * value can be read differently by.
     *
     * <p>Everything else a declaration is made of is compared. A form added to the language is
     * therefore compared by default, and something added that is <em>not</em> part of what a
     * declaration means has to be put here — which is a decision, made by whoever adds it, rather
     * than a silence.
     */
    private static final Set<Class<?>> ERASED = Set.of(
            SourcePos.class, Region.class,
            // Where a construction was carried in from, and what a coverage point was numbered as.
            // Both are records of how a declaration reached where it stands, kept for questions this
            // compile answers about itself; neither is anything a value crossing is read by.
            souther.compiler.types.ConstructionOrigin.class,
            souther.compiler.types.CoverageOrigin.class,
            // A binding's identity, which is its owner and the order it was reached in. Two builds
            // number their bindings by walking them, so this says a declaration was read rather than
            // saying anything the declaration says.
            souther.compiler.types.BindingId.class);

    /** Where the forms of the grammar are written. */
    private static final String GRAMMAR = "souther.compiler.ast.";

    /**
     * The forms a declaration is made of that are not written in the grammar.
     *
     * <p>Each is part of what a declaration means rather than of how it got here: which kind of thing
     * a name denotes ({@code ValueName} — a bare name meaning a standard-library function and one
     * meaning a local are two declarations), what a binding belongs to, and what a map's keys are
     * represented as at a boundary. They are named one by one because being outside the grammar is
     * where the question has to be asked.
     */
    private static final Set<String> MEANT_OUTSIDE_THE_GRAMMAR = Set.of(
            "souther.compiler.types.ValueName",
            "souther.compiler.types.BindingOwner",
            "souther.compiler.types.MapKeyRepresentation");

    /**
     * Whether {@code type} is a form a declaration is made of, compared part by part.
     *
     * <p>The grammar's own forms are, and so are the few named ones that are not written in it. A
     * record from anywhere else is neither: it arrived with a declaration rather than being part of
     * one, and what to do about it is a decision rather than a default.
     */
    static boolean isAFormOfTheGrammar(Class<?> type) {
        if (!type.isRecord()) {
            return false;
        }
        String name = type.getName();
        if (name.startsWith(GRAMMAR)) {
            return true;
        }
        for (String meant : MEANT_OUTSIDE_THE_GRAMMAR) {
            if (name.equals(meant) || name.startsWith(meant + "$")) {
                return true;
            }
        }
        return false;
    }

    /** Whether the comparison erases {@code type}. Asked by what holds this rule to covering every
     *  form a declaration can be made of, so that the two cannot come to disagree. */
    static boolean erases(Class<?> type) {
        return ERASED.contains(type);
    }

    /**
     * The types a declaration bottoms out in, compared as themselves.
     *
     * <p>Named rather than left to {@code equals}, so that a type reached here and classified by
     * nobody stops the comparison instead of being compared by whatever equality it happens to
     * have. That is the whole of the rule this walk is: a form is a record and is compared part by
     * part, a form is one of these and is compared as a value, or a person decides which it is.
     */
    static boolean comparedAsAValue(Class<?> type) {
        return type == String.class || type == Boolean.class || type == Integer.class
                || type == Long.class || type == Character.class || type == Double.class
                // A number a declaration states — the bound of an invariant, a default. Which
                // numbers it admits is what it says, and `1.0m` and `1.00m` are one number here as
                // they are everywhere else in the language, so the two are compared by amount rather
                // than by how they were written ({@code sameNumber}).
                || type == java.math.BigDecimal.class
                // Which declaration a name means, by the module and name that declare it rather than
                // by the object standing for it. A field's type is this, and a field whose type is
                // another declaration is read by another decoder.
                || type == souther.compiler.types.TypeSymbol.class
                || type.isEnum();
    }

    /** What a reader of the failure is being asked to decide. */
    private static String unclassified(Class<?> type) {
        return type.getName() + " is part of a declaration and this comparison does not know what it"
                + " is. Decide whether what a value crossing between two builds is read by depends on"
                + " it: if it does, it is compared as a value (add it to `comparedAsAValue`); if it"
                + " cannot, it is where something is written or the like, and belongs in `ERASED`.";
    }

    private static Object read(RecordComponent part, Object of) {
        try {
            return part.getAccessor().invoke(of);
        } catch (ReflectiveOperationException e) {
            throw new IllegalStateException("a record component that cannot be read: " + part, e);
        }
    }

    private static <T> Map<String, T> byName(List<T> declarations,
                                             java.util.function.Function<T, String> name) {
        Map<String, T> byName = new LinkedHashMap<>();
        for (T declaration : declarations) {
            byName.put(name.apply(declaration), declaration);
        }
        return byName;
    }

    private static List<String> difference(Set<String> ours, Set<String> theirs) {
        List<String> only = new ArrayList<>();
        for (String name : ours) {
            if (!theirs.contains(name)) {
                only.add(name);
            }
        }
        for (String name : theirs) {
            if (!ours.contains(name)) {
                only.add(name);
            }
        }
        return only;
    }

    private static String first(List<String> names) {
        return names.isEmpty() ? "" : Objects.requireNonNull(names.get(0));
    }
}
