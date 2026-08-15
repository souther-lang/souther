package souther.compiler.meta;

import souther.compiler.ast.Hir;
import souther.compiler.ast.WrittenName;
import souther.compiler.check.Prelude;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.ConstructionOrigin;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.lang.reflect.RecordComponent;
import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * Holds the declarations an answer reads a row's values by against the declarations the row is
 * written for.
 *
 * <p><strong>This does not answer any question the front end answers.</strong> Both sides are read
 * through {@link PublishedUniverse}, which puts a module's published declarations back together and
 * hands them to the compiler's own resolution; what arrives here already says which declaration
 * every name reaches, which binding a name is of, and what a type is. A bare name an import brought
 * in and the same name written out in full arrive alike, a renamed local arrives as the binding it
 * is, and nothing here has to know what a spelling means. What is decided here is only which of
 * those settled facts a value crossing between two builds depends on.
 *
 * <p>That is the whole of the split. A question about meaning — is this name that declaration, is
 * this binding that binding, is this number that number — belongs to the front end and is asked of
 * it. A question about crossing — does a decoder read a value differently if this changes — belongs
 * here and is answered nowhere else. The first kind arriving here is what this was rewritten to
 * stop: each one answered here is a rule of the language restated, and a restatement goes wrong in
 * its own way the day the language moves.
 *
 * <p>So what is compared is a projection and never a computation. Declarations come as the front end
 * settled them, and this drops the parts a crossing cannot see: where something was written, where a
 * body was spliced in from, what a coverage point was numbered as, and the {@code let}s no
 * declaration is read through. Whatever survives is compared as it stands.
 */
public final class DeclarationAgreement {

    private DeclarationAgreement() {}

    /**
     * Whether {@code theirs} declares {@code module}, and everything its declarations reach, as
     * {@code ours} does.
     *
     * <p>What a build carries and this compiler cannot read is answered ({@link Agreement.Unreadable})
     * rather than raised: an answer brings its classes from wherever it was built, and a run that let
     * that out would stop evaluating a module over one behavior's jar.
     *
     * @param module the module being evaluated, which is where the walk starts
     * @param ours   where the declarations the rows are written for are read from
     * @param theirs where the declarations the answer reads values by are read from
     */
    public static Agreement of(String module, PublishedModule.Classes ours,
                               PublishedModule.Classes theirs) {
        PublishedUniverse mine = PublishedUniverse.of(ours);
        PublishedUniverse yours = PublishedUniverse.of(theirs);
        Deque<String> toRead = new ArrayDeque<>(List.of(module));
        Set<String> read = new LinkedHashSet<>(List.of(module));
        while (!toRead.isEmpty()) {
            String name = toRead.removeFirst();
            Hir.Module ourSide = mine.resolved(name);
            Hir.Module theirSide = yours.resolved(name);
            if (ourSide == null) {
                return unreadable(name, mine, Agreement.Side.THE_MODULE_BEING_EVALUATED);
            }
            if (theirSide == null) {
                return unreadable(name, yours, Agreement.Side.THE_ANSWER);
            }
            Agreement said = agreed(name, ourSide, theirSide);
            if (!(said instanceof Agreement.Agree)) {
                return said;
            }
            // The modules the compared declarations reach into, read off what the front end resolved
            // each name to. Not the import lines: a module may import what only an unread helper
            // wanted, and may name a declaration in full with no import at all.
            //
            // The standard library is in neither. Nobody publishes it, and whether two builds have
            // the same one is what the boundary revision on each of them says.
            for (String reached : modulesReached(ourSide)) {
                if (read.add(reached)) {
                    toRead.addLast(reached);
                }
            }
        }
        return new Agreement.Agree();
    }

    /** Which of the two ways a module could not be read it was. */
    private static Agreement unreadable(String module, PublishedUniverse universe,
                                        Agreement.Side side) {
        return new Agreement.Unreadable(module,
                universe.declares(module) ? Agreement.Reason.NOT_READABLE_HERE
                        : Agreement.Reason.NOTHING_PUBLISHED,
                side);
    }

    /** Whether two readings of one module say the same thing about what a crossing depends on. */
    private static Agreement agreed(String module, Hir.Module ours, Hir.Module theirs) {
        Agreement types = held(module, byName(ours.defs(), Hir.Def::name),
                byName(theirs.defs(), Hir.Def::name), DeclarationAgreement::crossingParts);
        if (!(types instanceof Agreement.Agree)) {
            return types;
        }
        Agreement behaviors = held(module, byName(ours.behaviors(), Hir.BehaviorDef::name),
                byName(theirs.behaviors(), Hir.BehaviorDef::name),
                DeclarationAgreement::crossingParts);
        if (!(behaviors instanceof Agreement.Agree)) {
            return behaviors;
        }
        // A module publishes more `let`s than a declaration is read through: what it exposes travels
        // too, because a reader substitutes a value where it is named and expands a helper where it
        // is called. Those are read by whatever calls them, and a row's values crossing into an
        // answer never do — what they meet is what a declaration says, so what is compared is the
        // helpers a declaration cannot be read without.
        Set<String> readThrough = readThrough(ours);
        return held(module, byName(publishedHelpers(ours, readThrough), Hir.FnDef::name),
                byName(publishedHelpers(theirs, readThrough), Hir.FnDef::name),
                DeclarationAgreement::crossingParts);
    }

    /**
     * The declarations of one kind held against each other, by name.
     *
     * <p>A name only one side has is a difference in itself: a case added to a union, a type that was
     * removed. It is named as the declaration that differs, which is what it is.
     */
    private static <T> Agreement held(String module, Map<String, T> ours, Map<String, T> theirs,
                                      java.util.function.Function<T, List<Object>> parts) {
        for (Map.Entry<String, T> ourOwn : ours.entrySet()) {
            T theirOwn = theirs.get(ourOwn.getKey());
            if (theirOwn == null || !sameShape(parts.apply(ourOwn.getValue()),
                    parts.apply(theirOwn), new Bound())) {
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
     */
    private static List<Object> crossingParts(Hir.Def def) {
        return switch (def) {
            // Everything a product is: which declaration it is, whether it is a newtype (which is
            // what it is represented as), what it includes and holds, what it admits, and how it is
            // read and written.
            case Hir.Data d -> List.of(d.declares(), d.newtype(), d.includes(), named(d.fields()),
                    d.invariants(), d.decoder(), d.encoder());
            // Which cases a union has, and how one is told from another.
            case Hir.SumData s -> List.of(s.declares(), s.cases(), s.decoder(), s.encoder());
            // A unit is the declaration it is, which is what it was looked up by.
            case Hir.UnitData u -> List.of(u.declares());
        };
    }

    /** What a value crossing into a behavior depends on: what it takes and what it answers with. */
    private static List<Object> crossingParts(Hir.BehaviorDef behavior) {
        return switch (behavior) {
            case Hir.SpecBehavior b -> List.of(shaped(b.params()), b.ret(), b.constructs(),
                    b.dependsOn());
            // A composition does not arrive here. What a module publishes for one is the signature
            // its stages compute (`ModuleMetadata.signatureOf`), so what comes back from a jar is a
            // declared behavior like any other, and its stages are the module's own business. Said
            // as a refusal rather than as a comparison of the stages, because a comparison written
            // for a form that never arrives is a rule nobody can read the truth of.
            case Hir.PipeBehavior p -> throw new IllegalStateException(
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
    private static List<Object> crossingParts(Hir.FnDef fn) {
        return List.of(fn.params(), fn.declaredReturn() == null ? "" : fn.declaredReturn(),
                fn.body(), fn.modifiers());
    }

    /**
     * A data's fields, each as what it is called and what it holds.
     *
     * <p>A field's name is not a name of something else — it is what a decoder reads a value under,
     * so it is part of what the declaration says. Every other name in a declaration reaches something
     * and is compared as what it reaches; this one is compared as the word it is, which is why it is
     * lifted out here rather than left to the walk.
     */
    private static List<Object> named(List<Hir.Field> fields) {
        List<Object> shaped = new ArrayList<>();
        for (Hir.Field field : fields) {
            shaped.add(List.of(field.name(), field.type()));
        }
        return shaped;
    }

    /**
     * A behavior's parameters, as the types it takes in the order it takes them.
     *
     * <p>What a parameter is called is not part of what crosses: arguments are handed over by
     * position. A signature whose parameters are renamed takes what it took.
     */
    private static List<Object> shaped(List<Hir.Param> params) {
        List<Object> types = new ArrayList<>();
        for (Hir.Param param : params) {
            types.add(param.type());
        }
        return types;
    }

    /**
     * The helpers a declaration of {@code module} cannot be read without.
     *
     * <p>Read off what an invariant calls, as the front end resolved it: a helper of this module is
     * a {@link ValueName.Helper} of it, and reaching one reaches whatever it calls in turn.
     */
    private static Set<String> readThrough(Hir.Module module) {
        Map<String, Hir.FnDef> own = byName(module.fns(), Hir.FnDef::name);
        Set<String> reached = new LinkedHashSet<>();
        for (Hir.Def def : module.defs()) {
            if (def instanceof Hir.Data data) {
                for (Hir.InvariantClause clause : data.invariants()) {
                    reach(clause.expr(), module.name(), own, reached);
                }
            }
        }
        return reached;
    }

    /** Whatever {@code form} names of this module's own helpers, and what those reach in turn. */
    private static void reach(Object form, String module, Map<String, Hir.FnDef> own,
                              Set<String> reached) {
        for (String named : helpersNamedIn(form, module)) {
            Hir.FnDef fn = own.get(named);
            if (fn != null && reached.add(named)) {
                reach(fn.body(), module, own, reached);
            }
        }
    }

    /** The helpers of {@code module} a form names, as the front end answered each name. */
    private static Set<String> helpersNamedIn(Object form, String module) {
        Set<String> named = new LinkedHashSet<>();
        walk(form, new IdentityHashMap<>(), part -> {
            if (part instanceof ValueName.Helper helper && helper.module().equals(module)) {
                named.add(helper.name());
            }
        });
        return named;
    }

    /** The published helpers of {@code module} that are among {@code readThrough}. */
    private static List<Hir.FnDef> publishedHelpers(Hir.Module module, Set<String> readThrough) {
        List<Hir.FnDef> kept = new ArrayList<>();
        for (Hir.FnDef fn : module.fns()) {
            if (readThrough.contains(fn.name())) {
                kept.add(fn);
            }
        }
        return kept;
    }

    /**
     * The modules the compared declarations of {@code module} reach into.
     *
     * <p>Off what the front end resolved each name to: a type is the declaration it is, and a value
     * is the module's value it is. So a module reached by a name written out in full is here as
     * surely as one an import brought in, and one nothing compared names is not here however it was
     * imported.
     */
    private static Set<String> modulesReached(Hir.Module module) {
        List<Object> compared = new ArrayList<>(module.defs());
        compared.addAll(module.behaviors());
        compared.addAll(publishedHelpers(module, readThrough(module)));
        Set<String> reached = new LinkedHashSet<>();
        walk(compared, new IdentityHashMap<>(), part -> {
            if (part instanceof TypeSymbol type) {
                reached.add(type.module());
            }
            if (part instanceof ValueName.Helper helper) {
                reached.add(helper.module());
            }
            if (part instanceof ValueName.Behavior behavior) {
                reached.add(behavior.module());
            }
        });
        reached.remove(module.name());
        reached.removeIf(name -> name == null || name.isEmpty() || Prelude.isQualifier(name));
        return reached;
    }

    /**
     * Whether two settled forms are the same form.
     *
     * <p>A walk and not a rule. What each part means was decided before it got here, so what is left
     * is whether the two sides hold the same parts; the only thing decided here is which parts a
     * crossing cannot see, and those are named in {@link #ERASED}.
     */
    private static boolean sameShape(Object ours, Object theirs, Bound bound) {
        if (ours == null || theirs == null) {
            return ours == theirs;
        }
        if (ERASED.contains(ours.getClass())) {
            return ERASED.contains(theirs.getClass());
        }
        // A binding is not what it is called. The front end settled which binding every use is of,
        // so the two sides' identities are held to standing for each other and the uses follow —
        // both where a binding is introduced and where one is named, since a use carries the name it
        // was written with beside the identity that says which binding it is.
        if (ours instanceof BindingId ourBinding && theirs instanceof BindingId theirBinding) {
            return bound.bind(ourBinding, theirBinding);
        }
        if (ours instanceof ValueName.Local ourUse && theirs instanceof ValueName.Local theirUse) {
            return bound.bind(ourUse.id(), theirUse.id());
        }
        // A name that reaches something is what it reaches. The front end put that beside the
        // spelling it was written with and beside how it was reached; both of those are records of
        // the writing, and reading either would be reading how something was written.
        if (ours instanceof Hir.Var.Denoting ourUse && theirs instanceof Hir.Var.Denoting theirUse) {
            return sameShape(ourUse.denotes(), theirUse.denotes(), bound);
        }
        if (ours instanceof Hir.Name.Denoting ourType
                && theirs instanceof Hir.Name.Denoting theirType) {
            return sameShape(ourType.type(), theirType.type(), bound);
        }
        if (ours instanceof Optional<?> mine && theirs instanceof Optional<?> yours) {
            return sameShape(mine.orElse(null), yours.orElse(null), bound);
        }
        if (ours instanceof List<?> mine && theirs instanceof List<?> yours) {
            if (mine.size() != yours.size()) {
                return false;
            }
            for (int i = 0; i < mine.size(); i++) {
                if (!sameShape(mine.get(i), yours.get(i), bound)) {
                    return false;
                }
            }
            return true;
        }
        if (ours instanceof Set<?> mine && theirs instanceof Set<?> yours) {
            return mine.equals(yours);
        }
        if (ours instanceof Map<?, ?> mine && theirs instanceof Map<?, ?> yours) {
            return mine.keySet().equals(yours.keySet())
                    && mine.entrySet().stream()
                            .allMatch(e -> sameShape(e.getValue(), yours.get(e.getKey()), bound));
        }
        if (ours.getClass() != theirs.getClass()) {
            return false;
        }
        if (!ours.getClass().isRecord()) {
            // Whether two written values are one value is the language's answer, not this walk's:
            // `1.0m` and `1.00m` are one number wherever else two of them meet, and a comparison
            // deciding otherwise here would report a stale build over a difference the model does
            // not have.
            return souther.compiler.check.ConstEval.equal(ours, theirs);
        }
        for (RecordComponent part : ours.getClass().getRecordComponents()) {
            if (!sameShape(read(part, ours), read(part, theirs), bound)) {
                return false;
            }
        }
        return true;
    }

    /**
     * The parts of a settled declaration a value crossing cannot see.
     *
     * <p>Where something is written, where a body was spliced in from, and what a coverage point was
     * numbered as: each a record of how a declaration came to be where it is, kept for questions this
     * compile answers about itself.
     *
     * <p>A written name is here too, and that is what became of comparing spellings. What a
     * declaration is called is the key it is compared under ({@link #byName}); what a name reaches is
     * the symbol the front end resolved it to; the occurrence itself says nothing further, and
     * reading it would be reading how something was written rather than what it means.
     */
    private static final Set<Class<?>> ERASED = Set.of(
            SourcePos.class, Region.class, WrittenName.class,
            ConstructionOrigin.class, CoverageOrigin.class);

    /**
     * The bindings of one declaration, held to each other across the two builds.
     *
     * <p>What a binding is called is not something a value can be read differently by: a helper whose
     * parameter is renamed, with every use of it renamed too, admits exactly what it admitted. The
     * front end settled which binding every use is of, so what is left is to hold the two sides'
     * identities to standing for each other — both ways round, since two of ours may not both stand
     * for one of theirs.
     */
    private static final class Bound {

        private final Map<BindingId, BindingId> theirs = new LinkedHashMap<>();
        private final Map<BindingId, BindingId> ours = new LinkedHashMap<>();

        boolean bind(BindingId ourBinding, BindingId theirBinding) {
            BindingId already = theirs.put(ourBinding, theirBinding);
            BindingId alreadyOurs = ours.put(theirBinding, ourBinding);
            return (already == null || already.equals(theirBinding))
                    && (alreadyOurs == null || alreadyOurs.equals(ourBinding));
        }
    }

    /** Every part of {@code form}, once each. */
    private static void walk(Object form, Map<Object, Boolean> seen,
                             java.util.function.Consumer<Object> each) {
        if (form == null || seen.put(form, Boolean.TRUE) != null) {
            return;
        }
        each.accept(form);
        if (form instanceof Optional<?> maybe) {
            walk(maybe.orElse(null), seen, each);
            return;
        }
        if (form instanceof Iterable<?> many) {
            for (Object one : many) {
                walk(one, seen, each);
            }
            return;
        }
        if (form instanceof Map<?, ?> byKey) {
            for (Map.Entry<?, ?> entry : byKey.entrySet()) {
                walk(entry.getKey(), seen, each);
                walk(entry.getValue(), seen, each);
            }
            return;
        }
        if (!form.getClass().isRecord()) {
            return;
        }
        for (RecordComponent part : form.getClass().getRecordComponents()) {
            walk(read(part, form), seen, each);
        }
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
}
