package souther.compiler.meta;

import souther.compiler.stdlib.Stdlib;
import souther.compiler.Reserved;
import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
import souther.compiler.ast.RowPosition;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.crossing.DelegatedEqualityIsTheCrossingAnswer;
import souther.compiler.crossing.ObjectEqualityIsRepresentedByWhatItStandsFor;
import souther.compiler.crossing.ObjectEqualityIsTheCrossingAnswer;
import souther.compiler.types.BindingId;
import souther.compiler.ast.ConstructionOrigin;
import souther.compiler.types.ApplicationOrigin;
import souther.compiler.RecordOfTheBuilding;
import souther.compiler.SettledAnswer;
import souther.compiler.types.RuleOrigin;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.math.BigDecimal;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Consumer;

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
        return of(module, behavior, ours, theirs, stdlib, NobodyIsWatching.INSTANCE);
    }

    /**
     * The same crossing, with the forms whose comparison it left to an equality told to
     * {@code watching}.
     *
     * <p>For a reading of what this walk does, and open to the package for that. Which forms those
     * are is a question about this comparison and is answered by running it: worked out instead
     * from the rule that chooses the mode, the answer would be that rule restated, which is the
     * reading that cannot come out false.
     *
     * <p>Told and not asked, so the comparison answers what it would have answered. Nothing here
     * reads what the watcher does with it.
     */
    static Agreement of(String module, String behavior, PublishedClasses ours,
                        PublishedClasses theirs, Stdlib stdlib, Consumer<Class<?>> watching) {
        return new Crossing(PublishedUniverse.of(ours, stdlib), PublishedUniverse.of(theirs, stdlib),
                watching)
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

        private final Consumer<Class<?>> watching;

        private Crossing(PublishedUniverse mine, PublishedUniverse yours,
                         Consumer<Class<?>> watching) {
            this.mine = mine;
            this.yours = yours;
            this.watching = watching;
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
            if (ours == null || theirs == null
                    || !sameShape(ours, theirs, new Walk(new Bound(), watching))) {
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
            case Hir.Data d -> CrossingProjection.read(CrossingProjection.OF_A_PRODUCT, d);
            case Hir.SumData s -> CrossingProjection.read(CrossingProjection.OF_A_SUM, s);
            case Hir.UnitData u -> CrossingProjection.read(CrossingProjection.OF_A_UNIT, u);
        };
    }

    /** What a value crossing into a behavior depends on: what it takes and what it answers with. */
    private static List<Object> crossingParts(Hir.BehaviorDef behavior) {
        return switch (behavior) {
            case Hir.SpecBehavior b ->
                    CrossingProjection.read(CrossingProjection.OF_A_DECLARED_BEHAVIOR, b);
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

    /** What a value crossing into a published helper depends on. */
    private static List<Object> crossingParts(Hir.FnDef fn) {
        return CrossingProjection.read(CrossingProjection.OF_A_HELPER, fn);
    }

    /**
     * Whether two settled forms are the same form.
     *
     * <p>A walk and not a rule. What each part means was decided before it got here, so what is left
     * is whether the two sides hold the same parts; the only thing decided here is which parts a
     * crossing cannot see, and those are named in {@link #ERASED}.
     */
    private static boolean sameShape(Object ours, Object theirs, Walk walk) {
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
            return walk.bound().bind(ourBinding, theirBinding);
        }
        if (ours instanceof ValueName.Local ourUse && theirs instanceof ValueName.Local theirUse) {
            return walk.bound().bind(ourUse.id(), theirUse.id());
        }
        // Where the front end put the answer beside the spelling, the answer is what is compared.
        // These are the forms that carry both, and each is compared by what it was settled to be:
        // the spelling beside it is how the author reached it, which two builds may write
        // differently and mean the same.
        if (ours instanceof Hir.Var.Denoting ourUse && theirs instanceof Hir.Var.Denoting theirUse) {
            return sameShape(ourUse.denotes(), theirUse.denotes(), walk);
        }
        if (ours instanceof Hir.Name.Denoting ourType
                && theirs instanceof Hir.Name.Denoting theirType) {
            return sameShape(ourType.type(), theirType.type(), walk);
        }
        if (ours instanceof Hir.Binder ourBinding && theirs instanceof Hir.Binder theirBinding) {
            return sameShape(ourBinding.binding(), theirBinding.binding(), walk);
        }
        if (ours instanceof Hir.TypeRef ourRef && theirs instanceof Hir.TypeRef theirRef) {
            return sameShape(ourRef.type(), theirRef.type(), walk)
                    && sameShape(ourRef.arg(), theirRef.arg(), walk)
                    && sameShape(ourRef.tupleElems(), theirRef.tupleElems(), walk);
        }
        if (ours instanceof ValueName.OfType ourType && theirs instanceof ValueName.OfType theirType) {
            return sameShape(ourType.type(), theirType.type(), walk);
        }
        if (ours instanceof Optional<?> mine && theirs instanceof Optional<?> yours) {
            return sameShape(mine.orElse(null), yours.orElse(null), walk);
        }
        if (ours instanceof List<?> mine && theirs instanceof List<?> yours) {
            if (mine.size() != yours.size()) {
                return false;
            }
            for (int i = 0; i < mine.size(); i++) {
                if (!sameShape(mine.get(i), yours.get(i), walk)) {
                    return false;
                }
            }
            return true;
        }
        // A set, and the keys of a map, are compared by their own equality rather than by this walk.
        // That is right exactly where the two agree, and a value whose equality this comparison
        // would have answered differently about stops it rather than being held by a rule this
        // class does not control.
        if (ours instanceof Set<?> mine && theirs instanceof Set<?> yours) {
            // Both sides. What is being refused is a comparison by an equality this class does not
            // control, and that is what happens whichever side the value is on — read on one side
            // only, a declaration that lost its last entry has an empty set here and whatever their
            // build put in theirs goes through the guard it was written to meet.
            refuseWhatThisComparisonAnswersDifferently(mine);
            refuseWhatThisComparisonAnswersDifferently(yours);
            return mine.equals(yours);
        }
        if (ours instanceof Map<?, ?> mine && theirs instanceof Map<?, ?> yours) {
            refuseWhatThisComparisonAnswersDifferently(mine.keySet());
            refuseWhatThisComparisonAnswersDifferently(yours.keySet());
            return mine.keySet().equals(yours.keySet())
                    && mine.entrySet().stream()
                            .allMatch(e -> sameShape(e.getValue(), yours.get(e.getKey()), walk));
        }
        if (ours.getClass() != theirs.getClass()) {
            return false;
        }
        if (!StructuralParts.areHandedOver(ours.getClass())) {
            // Whether two written values are one value is the language's answer, not this walk's:
            // `1.0m` and `1.00m` are one number wherever else two of them meet, and a comparison
            // deciding otherwise here would report a stale build over a difference the model does
            // not have.
            //
            // Said after the decision and never before it. What is watching is told what this walk
            // handed over, this being the one place a form's whole comparison is left to an
            // equality; asked first, it would be a second author of which forms go that way.
            walk.handedToADelegatedEquality().accept(ours.getClass());
            return souther.compiler.check.ConstEval.equal(ours, theirs);
        }
        for (StructuralParts.Part part : StructuralParts.of(ours.getClass())) {
            if (!sameShape(part.of(ours), part.of(theirs), walk)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Refuses a collection holding a value this comparison would not have answered about the way
     * that value's own equality does.
     *
     * <p>A collection compares what it holds by that thing's own equality. Where the two agree
     * there is nothing to say; where they part, the collection has settled a question this class
     * was written to settle, and settled it by a rule nobody here chose. So what is refused is the
     * parting and not a kind of value — {@link #objectEqualityAnswersTheSame} is the whole of
     * what is asked.
     *
     * <p>Open to the package so what it refuses can be asked of it. Nothing in either build puts
     * such a value in a set today, so the walk cannot be made to arrive at one and a refusal nobody
     * can reach is a refusal nobody would notice going quiet — which is how the reading of forms one
     * door along came to see less without failing.
     */
    static void refuseWhatThisComparisonAnswersDifferently(Set<?> held) {
        for (Object one : held) {
            if (!objectEqualityAnswersTheSame(one)) {
                throw new IllegalStateException(one.getClass().getName()
                        + " is held in a set or used as a map key, and a collection compares what it"
                        + " holds by its own equality — which answers differently from this"
                        + " comparison about what it reads. Compare it the way this comparison"
                        + " does, or say why its equality is the right one.");
            }
        }
    }

    /**
     * Whether this comparison answers about {@code value} what the equality a collection asks of
     * any object does.
     *
     * <p>Two things, in this order: what this comparison does about a value, and what somebody has
     * said about what a collection does with it. The first is read off {@link #sameShape} and is
     * every way this answers something an equality would not — a part it passes over, a binding it
     * holds by what it stands for, a form it reads by the answer settled beside the spelling, a
     * container it reads through. The second is the account, and there is no third: a value nobody
     * has spoken for is refused.
     *
     * <p><b>What the walk does with a form is no answer here.</b> It was, and that was the defect:
     * a form the walk does not take apart goes to an equality, so both sides ask an equality and a
     * collection reaches what this reaches. It holds for every form the walk stops at, the one
     * whose equality reads what this comparison cannot see included — so this could not come out
     * false for exactly the forms whose holding rested on it. What a reader can take a form apart
     * into is no answer either, for the same reason one step in: those are the parts this
     * comparison reads, and what a collection reads is the equality, which a form written by hand
     * may have written to read anything at all.
     *
     * <p><b>Not the equality the walk hands two written values to.</b> That one is the language's
     * answer about them, and a decimal written two ways is one value there and two objects here.
     * What is asked here is about a collection, and a form speaks to the two separately.
     *
     * <p>Asked of a value and not of a type, because that is what the arms dispatch on and what a
     * collection holds. A container says nothing about what it will hold, and a part declared as
     * something a reader here cannot name says nothing at all; asked of the value, there is no such
     * gap to answer across — what is in hand is what this comparison will meet.
     */
    static boolean objectEqualityAnswersTheSame(Object value) {
        return comparedTheSame(value, Collections.newSetFromMap(new IdentityHashMap<>()));
    }

    private static boolean comparedTheSame(Object value, Set<Object> asking) {
        if (value == null) {
            return true;   // held against null and nothing else, whoever is asking
        }
        if (!asking.add(value)) {
            return true;   // already being answered above, and a cycle reaches nothing new
        }
        if (erases(value.getClass()) || value instanceof BindingId
                || readByTheAnswerBesideItsSpelling(value.getClass())) {
            return false;
        }
        if (value instanceof Optional<?> maybe) {
            return comparedTheSame(maybe.orElse(null), asking);
        }
        if (value instanceof List<?> written) {
            for (Object one : written) {
                if (!comparedTheSame(one, asking)) {
                    return false;
                }
            }
            return true;
        }
        if (value instanceof Set<?> held) {
            for (Object one : held) {
                if (!comparedTheSame(one, asking)) {
                    return false;
                }
            }
            return true;
        }
        if (value instanceof Map<?, ?> keyed) {
            for (Map.Entry<?, ?> each : keyed.entrySet()) {
                if (!comparedTheSame(each.getKey(), asking)
                        || !comparedTheSame(each.getValue(), asking)) {
                    return false;
                }
            }
            return true;
        }
        // A record that says a collection may hold it is read as its components, a record being its
        // components and nothing else. Said and not taken from being a record: one can write an
        // equality out and read whatever its writer chose, and the components would then be
        // answering for something the record does not do. Which of the two a record is cannot be
        // told from the class, so what is asked of it here is the saying, and that the ones who say
        // it have the equality a record is given is held over the compiled classes
        // (`ARecordACrossingReachesKeepsTheEqualityARecordIsGivenTest`) — over the ones that say
        // it, which is what arrives here.
        if (value.getClass().isRecord() && value instanceof ObjectEqualityIsTheCrossingAnswer) {
            for (StructuralParts.Part part : StructuralParts.of(value.getClass())) {
                if (!comparedTheSame(part.of(value), asking)) {
                    return false;
                }
            }
            return true;
        }
        // What it names, walked by the rules the rest of this uses. The claim is that its equality
        // is the equality of that, so what is asked of it is what would be asked of what it named.
        if (value instanceof ObjectEqualityIsRepresentedByWhatItStandsFor named) {
            return comparedTheSame(named.standsFor(), asking);
        }
        if (value instanceof ObjectEqualityIsTheCrossingAnswer
                || OBJECT_EQUALITY_AGREES_WITH_CROSSING.contains(value.getClass())) {
            return true;
        }
        // Nobody has said so. What the walk does with a form is no answer here: read that way, a
        // form is safe to hold because the walk stopped at it, which is true of the form whose
        // equality reads what this comparison cannot see — and the reading could not come out
        // false for the forms whose holding rests on it.
        return false;
    }

    /**
     * Whether this comparison reads it by the answer the front end settled beside its spelling.
     *
     * <p>The forms {@link #sameShape} has an arm for, named because that is what they are:
     * what makes a form one of these is that the comparison reads it that way, and a form that grew
     * an answer and has no arm is read by how it was written whatever its shape suggests. That a
     * form with the shape has an arm is held beside the comparison rather than assumed here.
     */
    static boolean readByTheAnswerBesideItsSpelling(Class<?> type) {
        for (Class<?> arm : READ_BY_THE_ANSWER) {
            if (arm.isAssignableFrom(type)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The forms {@link #sameShape} reads by the answer. One arm each, and this says which.
     *
     * <p>A local is among them. What stands beside its spelling is which binding it is, and the arm
     * that reads it holds two of those to standing for each other rather than to being the same one
     * — a second thing an equality of it does not do, and the same passing over of the spelling.
     *
     * <p>The arms and only the arms. A form here is one {@link #sameShape} reads by the answer
     * instead of by the spelling, and {@code AFormThatCarriesItsAnswerIsComparedByItTest} holds the
     * two sides of that together: a reachable form carrying both has an arm, and an arm is for a
     * form carrying both. So this is a set nothing else may be put in to get an answer out of it.
     */
    private static final Set<Class<?>> READ_BY_THE_ANSWER = Set.of(
            Hir.Var.Denoting.class, Hir.Name.Denoting.class, Hir.Binder.class,
            Hir.TypeRef.class, ValueName.OfType.class, ValueName.Local.class);

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
            ConstructionOrigin.class, SourceConstructOrigin.class,
            // What a definition was made as, and what an example row's position contributes to
            // reading what is written at it. Both are this compile's record of how it built its own
            // tree: a module publishes its declarations and the helpers they are read through, and
            // neither a row nor the definition a pass mints for one is among them.
            DefinitionRole.class, RowPosition.class,
            // Which text a rule's owner was quoted from. An owner says which module and which
            // behavior wrote a rule, and two builds that disagree about that disagree about which
            // rule it is; the text it was read out of is the file it sits in, which a build may
            // rename without moving anything a value crossing meets.
            //
            // The kind and not the arm, which is what it has to be here: one build reads a module
            // from the source it holds and another reads the text a published module was put back
            // together as, so one rule has a different arm on each side as a matter of course. Two
            // builds being two builds is the difference this comparison exists not to report.
            QuotedFrom.class,
            // Which rule a source wrote. It is an identity, and the consumer that needs one is the
            // coverage that files what a row exercised: a body spliced into two call sites carries
            // the rule it was written as, and two rules written in one helper stay two.
            //
            // A crossing depends on what a rule says and not on the identity another reader files it
            // under. What is left after this is erased is the block itself — its parameters, what it
            // applies, and where it stands among the parts holding it — so a block added, removed,
            // moved or rewritten is reported by the structure that holds it, which is what a row
            // meeting that rule would meet differently.
            RuleOrigin.class,
            // Which construct of a source an application was written as. What the comparison holds
            // of an application is what it applies and what it is handed; where the author put it
            // is this compile's record of reading them, and is answered here the way the construct
            // it names is answered.
            //
            // This arm and not what it is an arm of. The others say an application is there because
            // a pass put it there, and what a pass was following is a question with answers of its
            // own; erased with this one, a call the author wrote and a call derived from one would
            // arrive as a single thing not compared.
            ApplicationOrigin.Written.class);

    /** The kinds a form can be erased as, for whoever holds each form to answering to one. */
    static Set<Class<?>> erasedKinds() {
        return ERASED;
    }

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
     *
     * <p>One of them and not the first of several. A form answering to two would be held equal by
     * whichever was reached first, which is an iteration order nothing writes down; that no form
     * does is held to by {@link #erasedKinds()} being asked of what a declaration reaches.
     */
    static Class<?> erasedAs(Class<?> type) {
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
     * <p>Two ways of being one, and the grammar says both. A node is written inside {@link Hir},
     * where being one of the tree's own kinds is what putting it there is for. A shape the nodes
     * hold — a name as written, and whatever is written beside it later — says so by being a
     * {@link Hir.Shape}, because a shape is its own file exactly when its readers wanted it there
     * and where it sits answers nothing about what it is.
     *
     * <p>Asked of the grammar and never of what surrounds a type. A package holds whatever its
     * author found convenient, so reading one would hand a form's account to anything written
     * beside the tree and take it from a shape written anywhere else; and the comparison's own
     * erasing is an answer about what a crossing can see, so subtracting it here would settle what
     * a thing is by what is done with it. Either way the account is bought with something nobody
     * decided, which is what an account is for.
     *
     * <p>So a record beside the tree gets nothing from being beside it. What this compile keeps
     * about its own building is answered where that is answered — the comparison erases it — and a
     * type that is neither is undecided and says so.
     *
     * <p>Which of them is a form, and not which of them is a record. A record is how most are
     * written and a node whose own subsystem settled on writing it by hand is a form all the same —
     * so what is asked is whether it is one of the tree's nodes or one of the shapes a node holds,
     * and an enum or an interface there is neither.
     */
    static boolean isAFormOfTheGrammar(Class<?> type) {
        if (type.isInterface() || type.isEnum()) {
            return false;
        }
        if (Hir.Shape.class.isAssignableFrom(type)) {
            return true;
        }
        return isDeclaredInsideHir(type)
                && (type.isRecord() || Hir.class.isAssignableFrom(type));
    }

    /** Where it is written, not what it implements. Several nodes stand for a part of one rather
     *  than for a node in their own right, so they are nested there without implementing it. */
    private static boolean isDeclaredInsideHir(Class<?> type) {
        for (Class<?> enclosing = type; enclosing != null;
                enclosing = enclosing.getEnclosingClass()) {
            if (enclosing == Hir.class) {
                return true;
            }
        }
        return false;
    }

    /**
     * Whether it is one of the front end's settled answers, whose parts are what a crossing depends
     * on.
     *
     * <p>Asked of the type, which says so. What the front end settles about a declaration — what a
     * type is, what a name reaches, how a map key crosses — is what a crossing depends on: a field
     * whose type moved is the plainest disagreement there is. And what this compile keeps about how
     * it built what it built is written beside it, so a rule reading where the file sits would hand
     * one answer to both.
     */
    static boolean isASettledAnswer(Class<?> type) {
        return SettledAnswer.class.isAssignableFrom(type);
    }

    /**
     * Whether it is one of the records this compile keeps about how it built what it built.
     *
     * <p>The third thing a form reachable from a declaration can be, beside a form of the grammar
     * and a settled answer. It says what the type is and not what this reads of one: which of them
     * a crossing passes over is said by {@link #ERASED}, and a type is often both — an application
     * the author wrote is a record of the building that a crossing is also blind to, and neither of
     * those is said by the other.
     */
    static boolean isARecordOfTheBuilding(Class<?> type) {
        return RecordOfTheBuilding.class.isAssignableFrom(type);
    }

    /**
     * The forms this comparison itself says may be left to the equality it hands them to.
     *
     * <p>The other half of that account. A form written here says it for itself
     * ({@link DelegatedEqualityIsTheCrossingAnswer}), which is where such a claim belongs — beside
     * what it is a claim about, so that a part added to the form meets it. These are not written
     * here and cannot say anything, so what is claimed about them is claimed by the comparison that
     * hands them over.
     *
     * <p>One row each and no rule they are chosen by. "A type the platform declares" is a
     * description of these five and not a reason any of them is right: a platform type with parts
     * whose equality read fewer of them would pass a rule like that, and what makes each of these
     * right is written beside it.
     *
     * <ul>
     *   <li>{@code String} — a word is what it spells, and there is nothing inside one to read.
     *   <li>{@code Boolean}, {@code Integer}, {@code Long} — a part written as a primitive, boxed
     *       on its way here. Two of them are one value exactly when the primitive was.
     *   <li>{@code BigDecimal} — what it is handed to is the language's answer about two written
     *       numbers, which is what a model means by one: {@code 1.0m} and {@code 1.00m} are one
     *       value wherever else they meet, and a comparison saying otherwise would report a stale
     *       build over a difference no model has. That is the one of these whose own
     *       {@code equals} answers something else, and it is the delegated equality and not that
     *       one that is claimed about.
     * </ul>
     */
    private static final Set<Class<?>> THIS_COMPARISON_SAYS_SO = Set.of(
            String.class, Boolean.class, Integer.class, Long.class, BigDecimal.class);

    /**
     * The forms this comparison says a collection may hold, of those that cannot say it themselves.
     *
     * <p>The same shape of account as the one above and a different claim, so a different list. A
     * set compares what it holds by the equality the platform asks of any object, and the list
     * above is about the equality the walk hands two written values to — which is the language's
     * answer about them, and the two part on exactly one of these.
     *
     * <p>{@code BigDecimal} is that one and is not here. Two written numbers of one amount are one
     * value to what the walk hands them to and two objects to a set, so a set of them holds apart
     * what a crossing holds together.
     *
     * <p><b>What is claimed is about the equality and no more.</b> A hashed set finds what it holds
     * by the number a value answers before it compares anything, so holding one is also a claim
     * that the number and the equality agree — which these four keep because the platform's own
     * values keep it, and which is not a thing this list is the place to decide about for anything
     * else.
     */
    private static final Set<Class<?>> OBJECT_EQUALITY_AGREES_WITH_CROSSING = Set.of(
            String.class, Boolean.class, Integer.class, Long.class);

    /** The forms this comparison speaks for. Open to the package so a sweep over what is handed
     *  over can ask, and can ask what is in it rather than only about one form at a time. */
    static Set<Class<?>> saidByThisComparison() {
        return THIS_COMPARISON_SAYS_SO;
    }

    /**
     * What one comparison of two declarations carries as it goes.
     *
     * <p>The bindings held to each other so far, and whatever is watching what the walk decided.
     * Both belong to one comparison and to no other — two crossings compared at once are two sets
     * of bindings and two watchers — so they are carried rather than kept anywhere a second walk
     * could reach them.
     *
     * <p>What is watching is told and never asked. It hears which forms this walk left to an
     * equality, after the walk decided to; a watcher consulted about whether to would be a
     * second author of a decision this class makes, which is the shape the reading of that decision
     * is trying to get out of.
     *
     * @param bound              the two builds' bindings, held to standing for each other
     * @param handedToADelegatedEquality told the class of every form handed to its own equality
     */
    private record Walk(Bound bound, Consumer<Class<?>> handedToADelegatedEquality) {}

    /** What a walk nobody is watching is told, which is every walk but a reading of what one
     *  decided. Told and dropped: what a crossing answers does not depend on anyone hearing it. */
    private enum NobodyIsWatching implements Consumer<Class<?>> {
        INSTANCE;

        @Override
        public void accept(Class<?> form) {
        }
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
        if (!StructuralParts.areHandedOver(form.getClass())) {
            return;
        }
        for (StructuralParts.Part part : StructuralParts.of(form.getClass())) {
            walk(part.of(form), seen, each);
        }
    }

}
