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
            // The imports of the module as it is being evaluated are the ones followed: what the rows
            // are written for is what a value crossing has to be readable by. An import only the
            // other side has is a declaration of theirs nothing here reaches.
            for (Ast.Import imported : mine.published().module().imports()) {
                // The standard library is not published by anyone: it is what a compiler has, and
                // whether two builds have the same one is what the boundary revision on each of them
                // says. There is nothing here to read on either side, and a walk that read the
                // absence as a failure would refuse every module that imports `String`.
                if (!Prelude.isQualifier(imported.module()) && read.add(imported.module())) {
                    toRead.addLast(imported.module());
                }
            }
        }
        return new Agreement.Agree();
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
        Agreement types = held(module, byName(ours.module().defs(), Ast.Def::name),
                byName(theirs.module().defs(), Ast.Def::name), DeclarationAgreement::crossingParts);
        if (!(types instanceof Agreement.Agree)) {
            return types;
        }
        Agreement behaviors = held(module,
                byName(ours.module().behaviors(), Ast.BehaviorDef::name),
                byName(theirs.module().behaviors(), Ast.BehaviorDef::name),
                DeclarationAgreement::crossingParts);
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
                DeclarationAgreement::crossingParts);
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
        // An import binds names, and a name bound to another module is another declaration under the
        // same spelling. The modules themselves are compared by following them; what is compared here
        // is what each import brings into scope and under which qualifier — of the names the
        // declarations compared above are actually written with.
        Set<String> written = namesWritten(compared(ours.module(), readThrough));
        if (!sameShape(bindings(ours.module(), written),
                bindings(theirs.module(), namesWritten(compared(theirs.module(), readThrough))))) {
            return new Agreement.Disagree(module, "import");
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
                                      java.util.function.Function<T, List<Object>> parts) {
        for (Map.Entry<String, T> mine : ours.entrySet()) {
            T yours = theirs.get(mine.getKey());
            if (yours == null || !sameShape(parts.apply(mine.getValue()), parts.apply(yours))) {
                return new Agreement.Disagree(module, mine.getKey());
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
            // A composition publishes the signature its stages compute, so this is what a reader of
            // the published declarations sees rather than what it was written as. Its stages are the
            // module's own business and are not carried. Its declared output is optional, like a
            // helper's, and stands for itself when it is not written.
            case Ast.PipeBehavior p -> List.of(p.stages(),
                    p.declaredOut() == null ? "" : p.declaredOut());
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
     * What each import brings into scope, by the module it brings it from — of the names something
     * compared here is written with.
     *
     * <p>A module publishes more than a crossing is read through, and its import lines are what all
     * of it needed. An import only an unread helper wanted is not part of what a declaration says
     * any more than that helper is, and comparing it would report a build that changed nothing but
     * the thing this just decided not to compare.
     *
     * <p>The names as a set, since an import list is which names it brings in and not the order they
     * are written in. By what each name is rather than how it was spelled, for the reason every other
     * name here is compared that way.
     */
    private static Map<String, List<Object>> bindings(Ast.Module module, Set<String> written) {
        Map<String, List<Object>> bound = new LinkedHashMap<>();
        for (Ast.Import imported : module.imports()) {
            Set<String> brought = new LinkedHashSet<>();
            for (Ast.ImportedName name : imported.importedNames()) {
                if (written.contains(name.written().canonical())) {
                    brought.add(name.written().canonical());
                }
            }
            String alias = imported.alias() == null ? "" : imported.alias();
            if (brought.isEmpty() && !reachedUnder(alias, written)
                    && !reachedUnder(imported.module(), written)) {
                continue;   // nothing compared here is written with anything this brings in
            }
            bound.put(imported.module(), List.of(alias, brought));
        }
        return bound;
    }

    /** Whether any name written here is qualified by {@code qualifier}. */
    private static boolean reachedUnder(String qualifier, Set<String> written) {
        if (qualifier.isEmpty()) {
            return false;
        }
        for (String name : written) {
            if (name.startsWith(qualifier + ".")) {
                return true;
            }
        }
        return false;
    }

    /**
     * Every name written in the declarations being compared.
     *
     * <p>Over the same forms the comparison walks, so what an import is held to bringing in is
     * exactly what those forms are written with. A name that appears only in something not compared
     * is not here, which is the point.
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
        if (form instanceof String spelled) {
            // A name a form holds as text — what a call is written as, what a type names.
            into.add(spelled);
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
    private static boolean sameShape(Object ours, Object theirs) {
        if (ours == null || theirs == null) {
            return ours == theirs;
        }
        if (ERASED.contains(ours.getClass())) {
            return ERASED.contains(theirs.getClass());
        }
        if (ours instanceof WrittenName mine && theirs instanceof WrittenName yours) {
            return mine.canonical().equals(yours.canonical());
        }
        if (ours instanceof Optional<?> mine && theirs instanceof Optional<?> yours) {
            return sameShape(mine.orElse(null), yours.orElse(null));
        }
        if (ours instanceof List<?> mine && theirs instanceof List<?> yours) {
            if (mine.size() != yours.size()) {
                return false;
            }
            for (int i = 0; i < mine.size(); i++) {
                if (!sameShape(mine.get(i), yours.get(i))) {
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
                            .allMatch(e -> sameShape(e.getValue(), yours.get(e.getKey())));
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
            if (!sameShape(read(part, ours), read(part, theirs))) {
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
