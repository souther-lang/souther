package souther.compiler.meta;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.Reserved;
import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.ast.ConstructionOrigin;
import souther.compiler.types.CoverageOrigin;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.WrittenOwner;
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
     * Whether the declarations {@code behavior}'s crossing depends on say the same thing in both
     * builds.
     *
     * <p>Asked of one behavior, because that is what an answer is of. A row is handed to what
     * answers one behavior, and what crosses is what that behavior takes and answers with — so a
     * declaration the behavior does not reach is one no row of it ever meets, and holding two builds
     * to it reports a stale build for editing something else in the same file.
     *
     * <p>What a build carries and this compiler cannot read is answered ({@link Agreement.Unreadable})
     * rather than raised: an answer brings its classes from wherever it was built, and a run that let
     * that out would stop evaluating a module over one behavior's jar.
     *
     * @param module   the module being evaluated
     * @param behavior the behavior whose answer is being held to it
     * @param ours     where the declarations the rows are written for are read from
     * @param theirs   where the declarations the answer reads values by are read from
     */
    public static Agreement of(String module, String behavior, PublishedClasses ours,
                               PublishedClasses theirs, Stdlib stdlib) {
        return new Crossing(PublishedUniverse.of(ours, stdlib), PublishedUniverse.of(theirs, stdlib))
                .heldFrom(new ValueName.Behavior(module, behavior));
    }


    /**
     * The closure of what one behavior's crossing depends on, held across two builds as it is found.
     *
     * <p>One walk, and everything comes out of it. What is compared, which modules have to be read
     * for the comparing, and which helpers are part of a declaration are not three questions with
     * three rules: they are the reachable set of one projection — {@link #crossingParts} — from one
     * behavior. Written as three, a helper reached through an invariant was found and one reached
     * through an encoder was not, and neither rule said anything that would have told you.
     *
     * <p>Both builds are followed, not one. A declaration or a helper only one side reaches is one
     * side's answer about what its values are, and following only ours would compare the two by what
     * only one of them says a crossing is made of.
     */
    private static final class Crossing {

        private final PublishedUniverse mine;
        private final PublishedUniverse yours;
        private final Map<String, PublishedUniverse.Read> ourSide = new LinkedHashMap<>();
        private final Map<String, PublishedUniverse.Read> theirSide = new LinkedHashMap<>();
        private final Deque<Reached> toCompare = new ArrayDeque<>();
        private final Set<Reached> reached = new LinkedHashSet<>();

        private Crossing(PublishedUniverse mine, PublishedUniverse yours) {
            this.mine = mine;
            this.yours = yours;
        }

        /** What the two builds say about everything {@code behavior}'s crossing reaches. */
        Agreement heldFrom(ValueName.Behavior behavior) {
            // Compared, not reached. What `reach` decides is which of the things a walk finds a
            // crossing follows, and the behavior asked about was not found — it is what this was
            // given. Put through `reach`, a root it declined would come back `Agree` while nothing
            // had been held at all, which is an answer this may not give.
            //
            // No caller reaches that today: the one there is passes the module being evaluated,
            // which a compilation refuses to let take a reserved name. So this is what the method
            // says rather than a case anything meets, and the root it would decline is said as a
            // mistake by `notInSight` instead of answered.
            Reached root = new Reached.ABehavior(behavior);
            reached.add(root);
            toCompare.addLast(root);
            while (!toCompare.isEmpty()) {
                Agreement said = held(toCompare.removeFirst());
                if (!(said instanceof Agreement.Agree)) {
                    return said;
                }
            }
            return new Agreement.Agree();
        }

        /** One reached thing, held across the two builds, and whatever it reaches reached. */
        private Agreement held(Reached what) {
            Agreement missing = notInSight(what.module());
            if (missing != null) {
                return missing;
            }
            PublishedUniverse.Read here = ourSide.get(what.module());
            PublishedUniverse.Read there = theirSide.get(what.module());
            List<Object> ours = what.partsIn(here.module());
            List<Object> theirs = what.partsIn(there.module());
            // A name only one side has is a difference in itself: a type that was removed, a helper
            // one build's declaration is read through and the other's is not.
            if (ours == null || theirs == null || !sameShape(ours, theirs, new Bound())) {
                return new Agreement.Disagree(what.module(), what.name());
            }
            // Where a behavior's body comes from is not in a declaration and does not survive as
            // source, so it travels beside the module. It decides whether an implementation may be
            // supplied for a behavior at all, which is as much a fact about the crossing as the
            // signature is: two builds that disagree about it disagree about whether anything may
            // be handed in there. The whole state and not one of its readings — two builds calling
            // a behavior unwritten and injected respectively agree about neither. Asked of the
            // behaviors this crossing reaches, like everything else — the module's other behaviors
            // are nothing a row of this one meets.
            if (what instanceof Reached.ABehavior
                    && !java.util.Objects.equals(
                            here.behaviorImplementations().get(what.name()),
                            there.behaviorImplementations().get(what.name()))) {
                return new Agreement.Disagree(what.module(), what.name());
            }
            follow(ours);
            follow(theirs);
            return new Agreement.Agree();
        }

        /**
         * Both readings of {@code module}, or the answer for a side that has none — null where both
         * are in sight.
         *
         * <p>Read when the walk first reaches it rather than up front. A module is read whole by
         * {@link PublishedUniverse}, which follows what its text reaches so that every name in it
         * can be answered; what is asked for here is narrower and is the crossing's.
         */
        private Agreement notInSight(String module) {
            // Not a second place the language is left out — `reach` decides that, and this states
            // what has to be true once it has. A reserved name arriving here is a walk that reached
            // something nobody publishes, which is this compiler's mistake and not an author's:
            // both sides would answer `SaysNothing`, and what an author would be shown is E1927
            // asking for a dependency on `souther`, which no artifact carries and no model can add
            // (#1049). Raised rather than returned, so that a route opened later fails where it is
            // written instead of arriving at a reader as advice that cannot be taken.
            if (Reserved.isNamespace(module)) {
                throw new IllegalStateException("`" + module + "` is the language's own namespace,"
                        + " which no build publishes, so a crossing does not read declarations of"
                        + " it: whether two builds have the same ones is what the boundary revision"
                        + " on each of them says");
            }
            if (ourSide.containsKey(module)) {
                return null;
            }
            // What each side answered, taken as it was answered. Which of the ways a module could
            // not be read it was used to be worked out here by asking the classes a second, coarser
            // question, so a reader was told that what was published cannot be read here whatever
            // had actually gone wrong — a dependency the answer's classes leave out reads the same
            // as an artifact from another compiler.
            // A switch over the states there are rather than a test and a cast: the cast would work
            // the answer out a second time, and what a reading hands over is something this holds
            // from the type rather than from having just ruled the other states out.
            PublishedUniverse.Read here;
            switch (mine.resolved(module)) {
                case Readback.NotReady<PublishedUniverse.Read> notRead -> {
                    return new Agreement.Unreadable(notRead,
                            Agreement.Side.THE_MODULE_BEING_EVALUATED);
                }
                case Readback.Ready<PublishedUniverse.Read>(PublishedUniverse.Read read) ->
                        here = read;
            }
            PublishedUniverse.Read there;
            switch (yours.resolved(module)) {
                case Readback.NotReady<PublishedUniverse.Read> notRead -> {
                    return new Agreement.Unreadable(notRead, Agreement.Side.THE_ANSWER);
                }
                case Readback.Ready<PublishedUniverse.Read>(PublishedUniverse.Read read) ->
                        there = read;
            }
            // Both, or neither. Written down as each side is read, a side answered while the other
            // could not be would leave this module counting as one both sides have.
            ourSide.put(module, here);
            theirSide.put(module, there);
            return null;
        }

        /** Whatever {@code parts} names of a declaration, a behavior or a helper, reached. */
        private void follow(List<Object> parts) {
            walk(parts, new IdentityHashMap<>(), part -> {
                switch (part) {
                    case TypeSymbol type -> reach(new Reached.ADeclaration(type));
                    // Every kind of value name, written out. What the walk carries is `Object`, so
                    // the outer switch is an open world and needs its default; a name that has
                    // arrived at `ValueName` is a closed one again, and stepping into it is what
                    // buys back the guarantee that type has — a case added there is a compile error
                    // here rather than a name silently followed by nothing. It was not: a library
                    // call fell through the default, so one spelling of a rule crossed and the same
                    // rule written as a `match` did not (#1049).
                    case ValueName value -> {
                        switch (value) {
                            case ValueName.Behavior behavior ->
                                    reach(new Reached.ABehavior(behavior));
                            case ValueName.Helper helper -> reach(new Reached.AHelper(helper));
                            // The standard library, for the reason the language's own declarations
                            // are left out of `reach`: nobody publishes it, and whether two builds
                            // have the same one is what the boundary revision on each says.
                            case ValueName.Stdlib _ -> { }
                            // A binding is not a declaration. Which binding a use is of is compared
                            // where the two sides' forms are held together (`sameShape`), and there
                            // is nothing beyond this name to reach.
                            case ValueName.Local _ -> { }
                            // A type written where a value goes. The declaration it names is
                            // reached as the type it is, from the same part.
                            case ValueName.OfType _ -> { }
                            // A meaning the language gives and no module declares: `None`, a
                            // rounding mode. Nothing publishes one.
                            case ValueName.Builtin _ -> { }
                        }
                    }
                    default -> { }
                }
            });
        }

        /**
         * Reaches one thing, once.
         *
         * <p>What the language declares is not one of them. Nobody publishes the primitives,
         * {@code Option}'s cases or the prelude's data — there is no {@code souther/$Module.class}
         * for either side's path to carry — and whether two builds have the same ones is what the
         * boundary revision on each of them says ({@link ModuleReadback#read}). Neither is anything
         * of no module: a signature written over a primitive names no declaration.
         *
         * <p>Asked of the identity, which is what has the answer. This used to hold the module name
         * against {@link Reserved#isQualifier}, and a qualifier is the surface spelling a call
         * writes — {@code List}, {@code Option} — never the module of a name resolution has already
         * settled. So the test was one no reached thing could pass, and a rule reaching
         * {@code Some} or {@code Int} through a {@code match} arm sent the walk after a module
         * nobody ships; what came back was E1927, telling an author to depend on {@code souther}
         * (#1049).
         */
        private void reach(Reached what) {
            String module = what.module();
            if (module == null || module.isEmpty() || what.isDeclaredByLanguage()) {
                return;
            }
            if (reached.add(what)) {
                toCompare.addLast(what);
            }
        }
    }

    /**
     * One thing a crossing reaches, as what it is and where it is declared.
     *
     * <p>Each says what of a module it is, and a module that has no such thing says so by answering
     * with nothing. Which is the same question for all three, asked of the three kinds of thing a
     * declaration's parts can name.
     */
    private sealed interface Reached {

        String module();

        String name();

        /** Whether the language declares it rather than a module of some compilation. Delegated to
         *  the identity this stands for, which is where the answer is
         *  ({@link TypeSymbol#isDeclaredByLanguage()}); read off {@link #module()} here, it would be
         *  the namespace rule restated a fourth time. */
        boolean isDeclaredByLanguage();

        /** What of {@code m} this is, as what a crossing depends on — null where m has no such
         *  thing. */
        List<Object> partsIn(Hir.Module m);

        record ADeclaration(TypeSymbol type) implements Reached {

            @Override
            public String module() {
                // What the language declares has no module of a compilation to name, and `reach`
                // has already left it out; answering null says the same thing twice rather than
                // making up a module for it.
                return type instanceof TypeSymbol.AtModule at ? at.module() : null;
            }

            @Override
            public String name() {
                return type.name();
            }

            @Override
            public boolean isDeclaredByLanguage() {
                return type.isDeclaredByLanguage();
            }

            @Override
            public List<Object> partsIn(Hir.Module m) {
                for (Hir.Def def : m.defs()) {
                    if (def.name().equals(name())) {
                        return crossingParts(def);
                    }
                }
                return null;
            }
        }

        record ABehavior(ValueName.Behavior behavior) implements Reached {

            @Override
            public String module() {
                return behavior.module();
            }

            @Override
            public String name() {
                return behavior.name();
            }

            @Override
            public boolean isDeclaredByLanguage() {
                return behavior.isDeclaredByLanguage();
            }

            @Override
            public List<Object> partsIn(Hir.Module m) {
                for (Hir.BehaviorDef b : m.behaviors()) {
                    if (b.name().equals(name())) {
                        return crossingParts(b);
                    }
                }
                return null;
            }
        }

        record AHelper(ValueName.Helper helper) implements Reached {

            @Override
            public String module() {
                return helper.module();
            }

            @Override
            public String name() {
                return helper.name();
            }

            @Override
            public boolean isDeclaredByLanguage() {
                return helper.isDeclaredByLanguage();
            }

            @Override
            public List<Object> partsIn(Hir.Module m) {
                for (Hir.FnDef fn : m.fns()) {
                    if (fn.name().equals(name())) {
                        return crossingParts(fn);
                    }
                }
                return null;
            }
        }
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
            // what it is represented as), what it includes and holds, and what it admits. How a
            // value of it crosses is read off exactly those, so comparing the derived
            // representation as well would be comparing the same fact twice — and this reads
            // declarations as resolution left them, where nothing has derived one.
            case Hir.Data d -> List.of(d.declares(), d.newtype(), d.includes(), named(d.fields()),
                    d.invariants());
            // Which cases a sum has. How one is told from another is derived from that and from
            // what each case is (`check.Boundary`), and both are reached: a case is followed to its
            // own declaration, where a unit and a product are compared as the different forms they
            // are. Held here as well, it would be the same fact compared twice.
            case Hir.SumData s -> List.of(s.declares(), s.cases());
            // A unit is the declaration it is, which is what it was looked up by.
            case Hir.UnitData u -> List.of(u.declares());
        };
    }

    /** What a value crossing into a behavior depends on: what it takes and what it answers with. */
    private static List<Object> crossingParts(Hir.BehaviorDef behavior) {
        return switch (behavior) {
            case Hir.SpecBehavior b -> List.of(shaped(b.params()), b.ret(), b.constructs(),
                    b.dependsOn(), b.ensures());
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
        // Erased on both sides, and the same one. Read as "either is erased, so they match", a
        // `SourcePos` held against a `Region` comes back equal — two different things called one
        // because neither is compared. What is erased is a part a crossing cannot see, not a slot
        // anything at all may turn up in.
        Class<?> weErase = erasedAs(ours.getClass());
        Class<?> theyErase = erasedAs(theirs.getClass());
        if (weErase != null || theyErase != null) {
            return weErase == theyErase;
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
        // Where the front end put the answer beside the spelling, the answer is what is compared.
        // These are the forms that carry both, and each is compared by what it was settled to be:
        // the spelling beside it is how the author reached it, which two builds may write
        // differently and mean the same.
        if (ours instanceof Hir.Var.Denoting ourUse && theirs instanceof Hir.Var.Denoting theirUse) {
            return sameShape(ourUse.denotes(), theirUse.denotes(), bound);
        }
        if (ours instanceof Hir.Name.Denoting ourType
                && theirs instanceof Hir.Name.Denoting theirType) {
            return sameShape(ourType.type(), theirType.type(), bound);
        }
        if (ours instanceof Hir.Binder ourBinding && theirs instanceof Hir.Binder theirBinding) {
            return sameShape(ourBinding.binding(), theirBinding.binding(), bound);
        }
        if (ours instanceof Hir.TypeRef ourRef && theirs instanceof Hir.TypeRef theirRef) {
            return sameShape(ourRef.type(), theirRef.type(), bound)
                    && sameShape(ourRef.arg(), theirRef.arg(), bound)
                    && sameShape(ourRef.tupleElems(), theirRef.tupleElems(), bound);
        }
        if (ours instanceof ValueName.OfType ourType && theirs instanceof ValueName.OfType theirType) {
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
        // A set, and the keys of a map, are compared by their own equality — which reads every part
        // of what they hold, including the parts erased here. That is right for the values they hold
        // today and wrong for a form, so a form arriving in one stops the comparison rather than
        // being compared by an equality that does not know what this does.
        if (ours instanceof Set<?> mine && theirs instanceof Set<?> yours) {
            // Both sides. What is being refused is a comparison by an equality this class does not
            // control, and that is what happens whichever side the form is on — read on one side
            // only, a declaration that lost its last entry has an empty set here and whatever their
            // build put in theirs goes through the guard it was written to meet.
            refuseForms(mine);
            refuseForms(yours);
            return mine.equals(yours);
        }
        if (ours instanceof Map<?, ?> mine && theirs instanceof Map<?, ?> yours) {
            refuseForms(mine.keySet());
            refuseForms(yours.keySet());
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
     * Refuses a collection that holds a form of a declaration.
     *
     * <p>What is held in one is compared by its own equality, and a form's equality reads where it
     * was written and which binding it is — the two things this erases. A form arriving here is
     * therefore compared by a rule this class does not control, which is a decision nobody made.
     */
    private static void refuseForms(Set<?> held) {
        for (Object one : held) {
            if (one != null && one.getClass().isRecord()) {
                throw new IllegalStateException(one.getClass().getName()
                        + " is a form of a declaration held in a set or used as a map key, and a"
                        + " collection compares what it holds by its own equality — which reads what"
                        + " this comparison erases. Compare it as a form, or say why its equality is"
                        + " the right one.");
            }
        }
    }

    /**
     * The parts of a settled declaration a value crossing cannot see.
     *
     * <p>Where something is written, where a body was spliced in from, and what a coverage point was
     * numbered as: each a record of how a declaration came to be where it is, kept for questions this
     * compile answers about itself.
     *
     * <p>A name is not here, and the rule about names is one rule rather than a list. Where the
     * front end settled what a name means and put the answer beside it — a use with its
     * {@link ValueName}, a type with its {@link TypeSymbol} — the answer is what is compared and the
     * spelling is passed over, which is what makes an alias and a name written out in full one name.
     * Everywhere else the spelling <em>is</em> the meaning: which field a value is read under is that
     * word, and a decoder reads it by that word.
     *
     * <p>Which way round to default matters. A spelling read where the front end had already
     * answered is a build reported as moved over how a name was written — noisy, and answered by
     * naming the settled form. A spelling passed over where nothing else says what it means is two
     * rules called one rule: {@code r.min} and {@code r.max} agreeing, and a row handed to an answer
     * that refuses what this model admits. So the spelling is read unless something beside it says
     * what it means.
     */
    private static final Set<Class<?>> ERASED = Set.of(
            SourcePos.class, Region.class,
            ConstructionOrigin.class, CoverageOrigin.class,
            // What a definition was made as, and what an example row's position contributes to
            // reading what is written at it. Both are this compile's record of how it built its own
            // tree: a module publishes its declarations and the helpers they are read through, and
            // neither a row nor the definition a pass mints for one is among them.
            DefinitionRole.class, RowPosition.class);

    /**
     * The records this comparison names, and says of each how two of them are held.
     *
     * <p>Only the ones that are not forms of the grammar. A form's parts are what a crossing depends
     * on and are held one by one, which is a decision about forms as such; these are records the
     * front end puts <em>beside</em> a form to say what it settled, and each is here because
     * something above says what to do with it rather than because a walk found its components.
     */
    private static final Set<Class<?>> NAMED = Set.of(
            BindingId.class, TypeSymbol.class,
            ValueName.Local.class, ValueName.Helper.class, ValueName.Behavior.class,
            ValueName.Stdlib.class, ValueName.OfType.class,
            // The spelling, where nothing beside it says what it means — which is the rule this
            // class states about names, and this is the form that carries one on its own. Compared
            // as the word it is, because that is what it means there.
            WrittenName.class,
            // Who wrote a construct, which is half of what tells one rule from another — the other
            // half being the number counted within it. Compared whole: two rules are one when one
            // owner counted them the same, and an owner read component by component would put the
            // text an owner of rows carries in front of a comparison that has no question about it.
            WrittenOwner.Declaration.class, WrittenOwner.Stated.class, WrittenOwner.Body.class,
            WrittenOwner.Examples.class, WrittenOwner.Fake.class);

    /** Whether the comparison passes over it: a part of a settled declaration a crossing cannot
     *  see. */
    static boolean erases(Class<?> type) {
        return erasedAs(type) != null;
    }

    /**
     * Which of the erased kinds {@code type} is, or null where it is not one.
     *
     * <p>The kind and not the class. Two of one kind are one thing not compared, so which arm of it
     * each side has is not compared either; two of different kinds are two things, and answering
     * that they match because neither is compared would hold a position against a coverage number.
     */
    private static Class<?> erasedAs(Class<?> type) {
        for (Class<?> erased : ERASED) {
            if (erased.isAssignableFrom(type)) {
                return erased;
            }
        }
        return null;
    }

    /**
     * Whether it is a form of the grammar — something a declaration is written as, whose parts are
     * held one by one.
     *
     * <p>Asked of where the type is declared rather than of a list. A form of the grammar is a
     * record of {@link Hir}, and a record that is not one arriving in a declaration is something the
     * compiler put there about itself: reading its components would make a crossing depend on which
     * pass wrote a node, which is not something a value can be read differently by.
     */
    static boolean isAFormOfTheGrammar(Class<?> type) {
        if (!type.isRecord()) {
            return false;
        }
        // Where it is written, not what it implements. A form of the grammar is declared inside
        // `Hir`, and several of them stand for a part of one rather than for a form in their own
        // right, so they are nested there without implementing it.
        for (Class<?> enclosing = type; enclosing != null;
                enclosing = enclosing.getEnclosingClass()) {
            if (enclosing == Hir.class) {
                return true;
            }
        }
        return false;
    }

    /** Whether the comparison names it and says how two of them are held, without going inside. */
    static boolean namedByTheComparison(Class<?> type) {
        return NAMED.contains(type);
    }

    /**
     * Whether it is one of the front end's settled answers, whose parts are what a crossing depends
     * on.
     *
     * <p>Where it is declared, again. What the front end settles about a declaration lives in
     * {@code souther.compiler.types} — what a type is, what a name reaches, how a map key crosses —
     * and a crossing depends on all of it: a field whose type moved is the plainest disagreement
     * there is.
     */
    static boolean isASettledAnswer(Class<?> type) {
        return type.isRecord() && type.getPackageName().equals(TypeSymbol.class.getPackageName());
    }

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
            BindingId already = theirs.get(ourBinding);
            BindingId alreadyOurs = ours.get(theirBinding);
            if (already != null || alreadyOurs != null) {
                // Each stands for one of the other's, so a pair that contradicts what is already
                // held is refused — and refused without being written down, so what is held stays
                // what was agreed rather than what was rejected.
                return theirBinding.equals(already) && ourBinding.equals(alreadyOurs);
            }
            theirs.put(ourBinding, theirBinding);
            ours.put(theirBinding, ourBinding);
            return true;
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

}
