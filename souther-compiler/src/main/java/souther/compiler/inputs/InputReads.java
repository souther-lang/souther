package souther.compiler.inputs;

import souther.compiler.check.AnIndexedMap;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.CalledBody;
import souther.compiler.check.CallArguments;
import souther.compiler.check.Choice;
import souther.compiler.check.ClosureUses;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ElementAnswer;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.Location;
import souther.compiler.check.OrderOfElements;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.check.ValueStanding;
import souther.compiler.check.ElementsWrittenOut;
import souther.compiler.check.FoldedValue;
import souther.compiler.check.WhatAnOptionHolds;
import souther.compiler.core.Core;
import souther.compiler.core.EnteredArm;
import souther.compiler.core.Kernel;
import souther.compiler.inputs.OnePerElement.ReadOff;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.BuiltFrom;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.semantics.MapPart;
import souther.compiler.semantics.PieceOfAnElement;
import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.function.Function;
import java.util.function.Supplier;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;

/**
 * What a tree's names stand for, in terms of a behavior's input, where the reader has got to.
 *
 * <p>A reader meets a position under whatever name is in scope there, and the name is not the
 * position. Three things make that so, and one value carries them.
 *
 * <p>A tree may bind a name the behavior already binds. {@code let order = withDefaults(order)}
 * leaves every read below it naming the local, whose values are whatever the call answers with — so
 * a reader matching the word says about the parameter's rules what is true of nothing.
 *
 * <p>And a body reaches a position through the names bound on the way to it. A helper expanded into
 * a body binds the call's argument to the helper's own parameter and matches that, so a reader that
 * followed no binding would find every statement inside an expanded helper about a position it
 * cannot name — which is most of what a model's rules are written in.
 *
 * <p>And the parameters themselves are bound more than once. An implementation binds them where its
 * body reads them; the declaration binds them where its own {@code ensures} clauses do. Which
 * position a name points at is the same question in either tree, and which bindings ask it is not —
 * so the roots belong to the reading rather than to the input, and a reading given the other one's
 * finds every comparison about nothing.
 *
 * <p>And a name stands for more than a position or nothing. It is a position, or the expression it
 * was given, or one of several values this can write out, or an element an operation handed out, or
 * something this knows nothing about ({@link ReadMeaning}). Answered as a position and nothing, the
 * last four were one answer, and a rule written over a name given arithmetic over positions was read
 * as no rule at all.
 *
 * <p><b>Nothing here decides what a position holds.</b> That is {@link InputDomain}, and it is not
 * reachable from this: what a {@code Core.Read} met in a tree stands for and what the model says
 * about the location it stands at are two questions, asked of two values, meeting only where a
 * reader puts one answer to the other.
 *
 * <p>What is reachable is what the declaration puts at a path ({@link DeclaredInput}), which is no
 * reading and is there before one. A path is spelled the way the declaration names the location:
 * an arm selecting the one case the declaration leaves a value narrows nothing, and written as a
 * narrowing it would be a second spelling of a location the reading holds under the first.
 *
 * <p>Which is a difference in how long each of them lives, and not only in what each of them is
 * about. What is here is a function of the program point — the bindings gone under, the arm gone
 * into — and changes at every step of a walk. The reading is one value for a whole analysis. Held
 * in here it would be copied at every step, and a reader would ask whichever copy it had in hand.
 *
 * <p><b>What is known of the names is held and not published.</b> The environment answers the
 * questions a walk asks of it ({@link BindingEnvironment}), and which of its facts wins where a
 * binding is more than one of them is settled inside it — so a caller that reached the tables could
 * settle it again, in an order of its own, which is the whole of what that type is for. Nothing here
 * hands them out, and what a name comes to is asked rather than assembled.
 *
 * <p>What an arm narrowed is this reading's own and not the environment's. It is a fact about where
 * a walk is in the tree rather than about where a binding came from — read under one arm and not
 * under the next — so it is held beside the environment and put to it here.
 *
 * <p>And which of the behaviors a body calls a row stands in for. A call to one of them is a value a
 * row supplies, as a position's is, and a call to any other is one the model computes; which it is
 * is a fact about the body being read and not about the call, so a rule a declaration states, which
 * nothing stands a dependency in for, is read where none is.
 */
public final class InputReads {

    private static final ValueName.Stdlib.Operation GET = ValueName.Stdlib.operation("Map", "get");

    /** What an option is left where it holds a value. */
    private static final CasesLeft PRESENT = CasesLeft.of(Refinement.of(new Case.Presence(true)));

    private final BindingEnvironment names;
    private final Map<BindingId, List<ReadMeaning.Occurrence>> alternatives;
    private final DeclaredInput declared;
    private final souther.compiler.carrier.Membership<ValueName.Behavior> dependencies;
    private final Applied applied;
    /** {@link #hashCode}, worked out the first time it is asked: nothing here changes, and what it
     *  is worked out from holds every value bound on the way here. Nought where it has not been. */
    private int hash;
    /** Where each node {@link #pathOf} was asked of stands here, under the declarations
     *  {@link #pathsUnder}; null until it is first asked. No part of what this reading is. */
    private Map<Core, PathResolution> paths;
    private DeclarationNewtypes pathsUnder;

    /**
     * The applications of closures, the arms of choices and the calls of behaviors a reading here is
     * on.
     *
     * @param handed   the names an application handed one of the values written out, on the way
     *                 here ({@link #handing})
     * @param readings how many readings of one condition reading it here is one of: the product of
     *                 how many values each closure on the way down is applied to, and how many arms
     *                 each choice taken on the way down has ({@link #taking})
     * @param taken    what each value taken as another on the way down stands for, the latest
     *                 first; null where none was
     * @param given    what a name was handed that stands at no position and reads bindings of its
     *                 own, read where it was handed: a parameter of a behavior a call entered on the
     *                 way down ({@link #calling}), and one an application handed a value written out
     *                 ({@link #handing})
     * @param picked   the element of a list at an index written down that a name an arm opening
     *                 the lookup bound stands for ({@link WhatItHolds.AtAnIndex})
     * @param entered  the behaviors whose bodies were entered on the way down
     * @param widths   for each parameter a closure on the way down was applied through, how many
     *                 values it is handed: the applications of closures are among
     *                 {@code readings} as the product of these, the rest being the arms of
     *                 choices taken
     * @param turnsOn  for each name given a value, the names an application handed one of the
     *                 values written out that the value reads, as it was given ({@link
     *                 #standingFor}): a name may stand at a position, which says nothing of which
     *                 application chose it
     */
    private record Applied(Set<BindingId> handed, long readings, Taken taken,
                           Map<BindingId, Denotation> given,
                           Map<BindingId, PickedAtAnIndex> picked,
                           Set<ValueName.Behavior> entered, Map<BindingId, Long> widths,
                           Map<BindingId, Set<BindingId>> turnsOn) {

        static final Applied NONE = new Applied(Set.of(), 1, null, Map.of(), Map.of(), Set.of(),
                Map.of(), Map.of());

        Applied {
            handed = Set.copyOf(handed);
            given = Map.copyOf(given);
            picked = Map.copyOf(picked);
            entered = Set.copyOf(entered);
            widths = Map.copyOf(widths);
            turnsOn = Map.copyOf(turnsOn);
            long applications = applicationsOf(widths.values());
            if (readings % applications != 0) {
                throw new IllegalStateException("the applications of closures are among the"
                        + " readings a reading is one of, and so a factor of them: "
                        + applications + " of " + readings);
            }
        }

        private static long applicationsOf(Iterable<Long> widths) {
            long product = 1;
            for (long each : widths) {
                if (each < 1) {
                    throw new IllegalStateException("a parameter is handed some value: " + each);
                }
                product *= each;
            }
            return product;
        }

        /**
         * How many of {@code readings} are the applications of closures through parameters other
         * than {@code turnedOn}.
         */
        long applicationsNotThrough(Set<BindingId> turnedOn) {
            long product = 1;
            for (Map.Entry<BindingId, Long> each : widths.entrySet()) {
                if (!turnedOn.contains(each.getKey())) {
                    product *= each.getValue();
                }
            }
            return product;
        }

        /**
         * The same, as one of {@code readings} readings, the applications of closures among them
         * being those {@code widths} says, with {@code taken} for what was taken.
         */
        Applied as(long readings, Map<BindingId, Long> widths, Taken taken) {
            return new Applied(handed, readings, taken, given, picked, entered, widths, turnsOn);
        }
    }

    /**
     * What a reading takes a node as: another value, or a number of the arguments the node, a call,
     * was given.
     */
    private sealed interface TakenAs {

        /** Another value, read where it stands. */
        record AValue(Denotation value) implements TakenAs {}

        /** A form of the values the call the node is was given, read where the call stands. */
        record AFormOfItsArguments(LinearForm<Core> form) implements TakenAs {}
    }

    /**
     * That a reading here takes {@code node} as {@code as}, and what {@code older} says before it:
     * a choice as the answer of the arm the reading is on, a call of a behavior as the body it
     * enters, a call of an operation defined by cases as what the case the reading is on answers.
     *
     * <p>The node, and not one equal to it. A value is one value however often it is read, so two
     * reads of the node are taken alike; two written alike are two values, each taken its own way.
     *
     * <p>Its hash is worked out once and kept, and so is the hash of what the node is taken as. A
     * reading is a key wherever a walk asks whether it has been somewhere, and a reading is made
     * at every step of a walk over the same chain of takings: worked out again, each would walk
     * the whole chain, and each value a node is taken as is a tree.
     */
    private static final class Taken {

        private final Core node;
        private final TakenAs as;
        private final Taken older;
        /** {@code as.hashCode()}, nought where it has not been worked out. A copy of this taking
         *  over another chain holds the same {@code as} and starts from what this one knows. */
        private int asHash;
        /** {@link #hashCode}, nought where it has not been worked out. */
        private int hash;

        Taken(Core node, TakenAs as, Taken older) {
            this(node, as, 0, older);
        }

        private Taken(Core node, TakenAs as, int asHash, Taken older) {
            this.node = node;
            this.as = as;
            this.asHash = asHash;
            this.older = older;
        }

        /** What {@code e} is taken as, or null where it is not taken. */
        TakenAs of(Core e) {
            for (Taken at = this; at != null; at = at.older) {
                if (at.node == e) {
                    return at.as;
                }
            }
            return null;
        }

        /**
         * {@code more}, newest first, over this.
         *
         * <p>Without what of this {@code more} takes as well. {@link #of} reads the newest first, so
         * a node {@code more} takes is answered from {@code more} wherever it stands below; kept, it
         * would be one taking more for every value carried from a reading that was on it already,
         * and a chain carried down a run of choices would double at each of them.
         */
        Taken under(Taken more) {
            if (more == null) {
                return this;
            }
            // A value carried from a reading this one went on from holds this one's older takings
            // as they are, so most of the time there is nothing of this to keep.
            for (Taken at = more; at != null; at = at.older) {
                if (at == this) {
                    return more;
                }
            }
            Set<Core> newer = Collections.newSetFromMap(new IdentityHashMap<>());
            for (Taken at = more; at != null; at = at.older) {
                newer.add(at.node);
            }
            return more.over(without(newer));
        }

        /** This, with what takes one of {@code nodes} left out; null where nothing is left. */
        private Taken without(Set<Core> nodes) {
            Taken older = this.older == null ? null : this.older.without(nodes);
            if (nodes.contains(node)) {
                return older;
            }
            return older == this.older ? this : new Taken(node, as, asHash, older);
        }

        /** This, newest first, over {@code base}. */
        private Taken over(Taken base) {
            return base == null ? this
                    : new Taken(node, as, asHash, older == null ? base : older.over(base));
        }

        private int asHash() {
            int h = asHash;
            if (h == 0) {
                h = as.hashCode();
                asHash = h;
            }
            return h;
        }

        @Override
        public boolean equals(Object other) {
            if (this == other) {
                return true;
            }
            if (!(other instanceof Taken that) || node != that.node) {
                return false;
            }
            // Two whose hashes are known and differ hold different values somewhere down the chain.
            if (hash != 0 && that.hash != 0 && hash != that.hash) {
                return false;
            }
            return as.equals(that.as) && Objects.equals(older, that.older);
        }

        @Override
        public int hashCode() {
            int h = hash;
            if (h == 0) {
                h = Objects.hash(System.identityHashCode(node), asHash(), older);
                hash = h;
            }
            return h;
        }
    }

    /**
     * What {@code reading} comes to, with what it asked of the values handed on the way here.
     * Another reading that is this but for what was handed ({@link #sameButForWhatIsHanded}) and
     * hands the same answers ({@link #handsAsAsked}) is read to the same.
     */
    public <T> Watched<T> watchingWhatIsHanded(Supplier<T> reading) {
        return BindingEnvironment.Watch.over(names, reading);
    }

    /** Whether a reading is being watched on this thread, which a reading that skips part of
     *  itself would leave without what that part asked. */
    public static boolean watching() {
        return BindingEnvironment.Watch.running();
    }

    /** Whether the values handed on the way here are the ones {@code asked} was answered. */
    public boolean handsAsAsked(HandedAnswers asked) {
        return asked.holdsOf(names);
    }

    /** Whether {@code that} holds what this does, but for the values handed on the way to it. */
    public boolean sameButForWhatIsHanded(InputReads that) {
        return this == that || (alternatives.equals(that.alternatives)
                && declared.equals(that.declared)
                && dependencies.equals(that.dependencies)
                && applied.equals(that.applied)
                && names.sameButForWhatIsHanded(that.names));
    }

    /** A hash that two readings which are the same but for what was handed share. */
    public int hashButForWhatIsHanded() {
        return Objects.hash(names.hashButForWhatIsHanded(), applied.readings(), applied.widths(),
                applied.handed(), applied.taken());
    }

    private InputReads(BindingEnvironment names,
                       Map<BindingId, List<ReadMeaning.Occurrence>> alternatives,
                       DeclaredInput declared,
                       souther.compiler.carrier.Membership<ValueName.Behavior> dependencies,
                       Applied applied) {
        this.names = names;
        this.alternatives = Map.copyOf(alternatives);
        this.declared = declared;
        this.dependencies = Objects.requireNonNull(dependencies,
                "a body says which calls a row stands in for, if none");
        this.applied = Objects.requireNonNull(applied,
                "a reading is on some applications, if none");
    }

    /**
     * At the top of a body, where nothing has been bound yet and no element has been handed out.
     *
     * <p>The parameters as a naming and not as a reading of them. What a caller has in hand is
     * usually an {@link InputDomain}, which knows the same naming; taking the whole of it here
     * would put the reading back inside the walk to be reached for later, so what comes in is the
     * part this uses.
     *
     * <p>{@code declared} is what the declaration puts under those parameters, which is what says
     * how a position the body narrows is spelled ({@link DeclaredInput}). Given
     * {@link DeclaredInput#NONE}, every arm narrows the position it matched.
     *
     * <p>{@code elements} is what the operations that handed their closures the contents of
     * containers were read to say, since the tree this walks has none of them left in it. Given
     * nothing, every name inside a closure names no position.
     *
     * <p>{@code dependencies} is what a row stands in for ({@link InputDomain#dependencies}).
     *
     * <p>{@code values} is what the values the body builds are defined as. In this tree a value is
     * a call of its method, and what it is defined as is held in the other tree; handed none, every
     * such call is a call this reading knows nothing of.
     */
    public static InputReads ofParameters(
            Map<BindingId, String> parameters, DeclaredInput declared, ElementBindings elements,
            ValueDefinitions values,
            souther.compiler.carrier.Membership<ValueName.Behavior> dependencies) {
        return new InputReads(new BindingEnvironment(BindingEnvironment.rooted(parameters),
                Map.of(), elements, values, false), Map.of(), declared, dependencies,
                Applied.NONE);
    }

    /**
     * The same, at the top of the body the analysis reads.
     *
     * <p>Beside {@link #ofParameters} because the two are readings of two trees. That one is of the
     * body a backend emits, where an operation of the language has been expanded into what it does,
     * so one standing there says the walk was handed the wrong tree. Here they stand — that is what
     * the analysis reads the tree for — and a value one of them made names no position, which is an
     * answer rather than a fault.
     *
     * <p>Its own entry point and not a flag on the one above, so that which tree a reading is of is
     * settled where the walk that reads it is written. Asked for afterwards, a walk of one tree
     * could be handed the other's reading and the first rule about a value an operation made would
     * be reported as this compiler failing to expand something.
     *
     * <p>The values this tree builds are defined in it, and read with its own bindings.
     */
    public static InputReads ofParametersWhereCallsStand(
            Map<BindingId, String> parameters, DeclaredInput declared, ElementBindings elements,
            souther.compiler.carrier.Membership<ValueName.Behavior> dependencies) {
        return new InputReads(new BindingEnvironment(BindingEnvironment.rooted(parameters),
                Map.of(), elements, ValueDefinitions.readWith(elements), true), Map.of(),
                declared, dependencies, Applied.NONE);
    }

    /**
     * Where the values this reading meets are read as what they are defined as: the reading a
     * definition of one is read in ({@link ValueDefinitions#reading}). A reader that walks the
     * definitions themselves walks them here, so that what a name inside one means is what it
     * means to a reading that followed a name into it.
     */
    public InputReads whereValuesAreDefined() {
        return names.values().reading();
    }

    /**
     * Where a value's definition is read ({@link ValueDefinitions#reading}): no parameter, nothing
     * declared under one, nothing a row stands in for, and the operations of the language standing
     * — the bindings the definitions make and what their operations hand their closures, and the
     * definitions of the values they name in turn.
     */
    static InputReads insideADefinition(ValueDefinitions values, ElementBindings definedWith) {
        return new InputReads(new BindingEnvironment(Map.of(), Map.of(), definedWith, values,
                true), Map.of(), DeclaredInput.NONE, souther.compiler.carrier.Membership.none(),
                Applied.NONE);
    }

    /**
     * At the top of a rule the behavior itself declares, which meets the parameters under the
     * bindings the declaration gave them rather than the ones an implementation did.
     *
     * <p>Which is why the bindings are handed in: a behavior nothing implements binds its
     * parameters nowhere a body could, and its clauses still name them.
     */
    public static InputReads ofWhatIsDeclared(Map<BindingId, String> roots,
                                              DeclaredInput declared) {
        return new InputReads(new BindingEnvironment(BindingEnvironment.rooted(roots), Map.of(),
                ElementBindings.NONE, ValueDefinitions.NONE, true), Map.of(), declared,
                souther.compiler.carrier.Membership.none(), Applied.NONE);
    }

    /**
     * The same, of a clause a declaration wrote about a value standing somewhere in the input.
     *
     * <p>Rooted at paths rather than at parameter names, which is what such a clause needs: it binds
     * the fields of the declaration that wrote it, and those fields stand wherever a value of that
     * declaration stands — under a parameter, under a field of one, under what a container holds. A
     * name here is a field's binding and never a parameter's, so there is no name to look a
     * parameter up by.
     *
     * <p>The operations the language defines the meaning of are left standing, as they are in every
     * reading of what a declaration wrote: that is the representation a declaration's own rules are
     * held in, and a clause read in the one that runs would have the calls in it gone.
     */
    public static InputReads ofADeclaredClause(Map<BindingId, TermPath> roots,
                                               DeclaredInput declared) {
        return new InputReads(new BindingEnvironment(roots, Map.of(),
                ElementBindings.NONE, ValueDefinitions.NONE, true), Map.of(), declared,
                souther.compiler.carrier.Membership.none(), Applied.NONE);
    }

    /**
     * An environment written out rather than read off a body.
     *
     * <p>For holding this reading to what it does over environments no source produces. A binding
     * that holds a value and is also what an operation handed an element on, or a run of names that
     * comes round to itself, are states of the environment rather than of a model, and what this
     * reading does with one is a rule it keeps whatever a body can be written to say.
     */
    static InputReads written(Map<BindingId, TermPath> roots, Map<BindingId, Core> bound,
                              ElementBindings elements) {
        return new InputReads(new BindingEnvironment(roots, bound, elements,
                ValueDefinitions.NONE, false), Map.of(),
                DeclaredInput.NONE, souther.compiler.carrier.Membership.none(), Applied.NONE);
    }

    /**
     * The same, on the application of a closure that hands {@code binding} {@code value}, one of the
     * values a container was written with.
     *
     * <p>Where an application reads a condition is where the name is one value and not the set of
     * them ({@link ReadMeaning.OneOf}), which is a fact about where a reading is, as an arm's
     * narrowing is. A value at a position is that position, as an arm's is. One that names nothing
     * is itself wherever it is read. One that names a binding of where it was written and stands at
     * no position is read where it was written, as what a call hands a parameter is
     * ({@link #calling}): its names are that reading's and not these.
     */
    public InputReads handing(BindingId binding, Denotation value, DeclarationNewtypes newtypes) {
        return handedAs(binding, value, newtypes).turningOn(binding, List.of(value));
    }

    private InputReads handedAs(BindingId binding, Denotation value, DeclarationNewtypes newtypes) {
        Map<BindingId, List<ReadMeaning.Occurrence>> narrower = new LinkedHashMap<>(alternatives);
        narrower.remove(binding);
        Set<BindingId> handed = new HashSet<>(applied.handed());
        handed.add(binding);
        if (value.at().pathOf(value.value(), newtypes) instanceof PathResolution.At(TermPath at)) {
            return new InputReads(names.naming(binding, at), narrower, declared, dependencies,
                    new Applied(handed, applied.readings(), applied.taken(), applied.given(),
                            applied.picked(), applied.entered(), applied.widths(),
                            applied.turnsOn()));
        }
        if (namesSomething(value.value())) {
            Map<BindingId, Denotation> given = new LinkedHashMap<>(applied.given());
            given.put(binding, value);
            return new InputReads(names, narrower, declared, dependencies, new Applied(handed,
                    applied.readings(), applied.taken(), given, applied.picked(),
                    applied.entered(), applied.widths(), applied.turnsOn()));
        }
        return new InputReads(names.handing(binding, value.value()), narrower, declared,
                dependencies, new Applied(handed, applied.readings(), applied.taken(),
                        applied.given(), applied.picked(), applied.entered(),
                        applied.widths(), applied.turnsOn()));
    }

    /**
     * Whether this reading is on an application of a closure: whether what is read here is
     * evaluated again on each value the closure is applied to.
     *
     * <p>That is a fact about where a thing is written and not about what it reads. A choice
     * written in a closure's body that reads nothing the closure was handed is still made on every
     * application.
     */
    public boolean isOnAnApplication() {
        return !applied.handed().isEmpty();
    }

    /** Whether an application this reading is on handed {@code binding} one of the values a
     *  container was written with ({@link #handing}). */
    public boolean hands(BindingId binding) {
        return applied.handed().contains(binding);
    }

    /**
     * Whether what {@code name} stands for turns on which application of a closure this reading is
     * on: whether it reads a name an application handed one of the values written out, itself or
     * through the names it was given.
     *
     * <p>Such a name is one value on each application and another on the next, so it is not one
     * value however it is read: a reader naming a value by its binding would name values of
     * different applications alike.
     */
    public boolean turnsOnAnApplication(Core.Read name) {
        if (applied.handed().isEmpty()) {
            return false;
        }
        Set<BindingId> turnedOn = new HashSet<>();
        applicationsRead(name, new HashSet<>(), turnedOn);
        return !turnedOn.isEmpty();
    }

    /**
     * Adds to {@code into} each name an application handed one of the values written out that
     * {@code e} reads, itself or through the names it was given. The applications through the
     * parameters left out are ones it is the same value on.
     */
    private void applicationsRead(Core e, Set<BindingId> met, Set<BindingId> into) {
        if (e instanceof Core.Read read) {
            if (applied.handed().contains(read.binding())) {
                into.add(read.binding());
            }
            if (met.add(read.binding())) {
                bindingRead(read, met, into);
            }
            return;
        }
        Core.forEachChild(e, child -> applicationsRead(child, met, into));
    }

    /**
     * What a name stands for, followed by how it was bound and not by where it stands: a name an
     * application handed a position stands at that position, and so does a name given that
     * parameter's field, and which application chose the position is told by the parameters the
     * value it was given reads ({@link #standingFor}), or by what a name it was bound to reads.
     */
    private void bindingRead(Core.Read read, Set<BindingId> met, Set<BindingId> into) {
        Set<BindingId> turnsOn = applied.turnsOn().get(read.binding());
        if (turnsOn != null) {
            into.addAll(turnsOn);
        } else if (names.roleOf(read.binding()) instanceof BindingRole.Alias(var value)
                && value != read) {
            applicationsRead(value, met, into);
        }
    }

    /**
     * Whether an operation over a list that stops at the first element meeting a statement that may
     * answer nothing is read in an order the rows choose: the bodies read here read no list's order
     * besides, and hold no second such operation ({@link OrderOfElements#leftToTheRows}).
     */
    public boolean orderLeftToTheRows() {
        return names.order().leftToTheRows();
    }

    /** How many readings of one condition reading it here is one of ({@link Applied#readings}). */
    public long readings() {
        return applied.readings();
    }

    /**
     * How far each operation handing {@code block}'s parameters the elements of a container goes
     * applying it: one for a parameter handed one container's elements, one for each container a
     * parameter is handed something of where several hand it. Empty where no parameter is handed
     * the elements of any — and a parameter handed values written out is read on each
     * application instead, so it is none of these.
     */
    public List<HowAClosureIsApplied> howItIsApplied(Core.Block block) {
        List<HowAClosureIsApplied> out = new ArrayList<>();
        for (Core.Binder param : block.params()) {
            if (param == null || param.binding() == null
                    || alternatives.containsKey(param.binding())) {
                continue;
            }
            switch (names.roleOf(param.binding())) {
                case BindingRole.Element(var held) -> out.add(held.applied());
                case BindingRole.ElementOfSeveral(var held) ->
                        held.forEach(each -> out.add(each.applied()));
                case BindingRole.Root _, BindingRole.Alias _, BindingRole.Unknown _ -> { }
            }
        }
        return List.copyOf(out);
    }

    /**
     * The containers {@code block} is applied over, read here, one for each operation applying it
     * — or empty where something other than an operation over a container may apply it.
     *
     * <p>A body entered by an application of the closure is entered only where one of these holds
     * something. Empty says nothing is known of what enters it, and not that nothing does.
     */
    public List<AppliedOver> containersAppliedOver(Core.Block block) {
        for (Core.Binder param : block.params()) {
            if (param != null && param.binding() != null) {
                List<HeldIn> handed = names.handedFrom(param.binding());
                return names.enteredOver(param.binding()).stream()
                        .map(container -> new AppliedOver(new Denotation(container, this),
                                handed.stream().anyMatch(each -> each.container() == container
                                        && each.ofAnOption())))
                        .toList();
            }
        }
        return List.of();
    }

    /**
     * Every use of {@code block}: each application an operation makes of it, and whether anything
     * else uses it — or null where no operation applies it. What is applied over is read where
     * these are the names ({@link Denotation}).
     */
    public ClosureUses usesOf(Core.Block block) {
        for (Core.Binder param : block.params()) {
            if (param != null && param.binding() != null) {
                return usesOfTheClosureTaking(param.binding());
            }
        }
        return null;
    }

    /**
     * What the body gave {@code name}, read here, where that is all the name is — or null where it
     * is a parameter, what an application handed, an element, or was given nothing.
     *
     * <p>Beside {@link #standing}, which stops at a name standing at a position of the input: that
     * is where it stands, and it is also a name for what it was given. {@code let d = l.discount}
     * stands at the element's discount, and {@code d} is {@code l.discount} — the same element's,
     * which the position alone does not say.
     */
    public Denotation givenTo(Core.Read name) {
        Core value = names.given(name.binding());
        return value == null ? null : new Denotation(value, this);
    }

    /** Every use of the closure {@code param} is a parameter of, or null where no operation
     *  applies it ({@link #usesOf}). */
    public ClosureUses usesOfTheClosureTaking(BindingId param) {
        return names.usesOf(param);
    }

    /**
     * A container a closure is applied over, and whether it is an option whose value it is handed:
     * then what the closure is applied to is that one value, and it is applied where the option
     * holds one.
     */
    public record AppliedOver(Denotation container, boolean anOption) {

        public AppliedOver {
            Objects.requireNonNull(container, "a closure is applied over some container");
        }
    }

    /**
     * What reading {@code block}'s body on each application of it that hands a parameter one of the
     * values a container was written with comes to.
     *
     * <p>Read here, at the closure, and not where a condition in its body is: a name the body binds
     * on the way to the condition is read where it was bound, which is inside an application and
     * after the parameter was handed its value.
     *
     * <p>Counted before anything is made. How many applications there are is the product of how
     * many values each parameter is handed, times the readings this one is already one of; past
     * {@code most}, none of them is made, so a closure nested in closures costs what the figure
     * allows and not what the nesting would. A container holding more than is written out is past
     * it already.
     *
     * <p>Each application is handed one occurrence of each container there on some row, as
     * {@code kept} decides, and is made only where the container holds it: what each occurrence is
     * still kept by goes with the application. A parameter handed the elements of a container that
     * holds none — written so, or with every occurrence dropped on every row — is handed nothing,
     * and the closure is applied to nothing ({@link Applications.NoneMade}).
     */
    public Applications applicationsOf(Core.Block block, Symbols symbols,
                                       DeclarationNewtypes newtypes, int most,
                                       ReadMeaning.WhereKept kept) {
        List<Core.Binder> handed = new ArrayList<>();
        List<List<ReadMeaning.Occurrence>> occurrencesOf = new ArrayList<>();
        HowAClosureIsApplied how = HowAClosureIsApplied.TO_EVERY_ELEMENT;
        long readings = applied.readings();
        for (int at = 0; at < block.params().size(); at++) {
            Core.Binder param = block.params().get(at);
            if (param == null || param.binding() == null) {
                continue;
            }
            Core.Read read = new Core.Read(param.name(), param.binding(),
                    block.paramTypes().get(at), block.pos());
            switch (meaningOf(read, symbols, newtypes)) {
                case ReadMeaning.OneOf one -> {
                    List<ReadMeaning.Occurrence> occurrences = one.occurrencesWhere(kept);
                    if (occurrences.isEmpty()) {
                        return new Applications.NoneMade();
                    }
                    if (!alternatives.containsKey(param.binding())
                            && names.roleOf(param.binding())
                                    instanceof BindingRole.Element(var held)) {
                        how = held.applied();
                    }
                    handed.add(param);
                    occurrencesOf.add(occurrences);
                    if (readings > most / occurrences.size()) {
                        return new Applications.MoreThanAreRead();
                    }
                    readings *= occurrences.size();
                }
                case ReadMeaning.NoneHeld _ -> {
                    return new Applications.NoneMade();
                }
                case ReadMeaning.MoreThanAreWrittenOut _ -> {
                    return new Applications.PastWhatIsWrittenOut();
                }
                case ReadMeaning.Position _, ReadMeaning.Through _, ReadMeaning.Element _,
                     ReadMeaning.Unknown _ -> { }
            }
        }
        if (handed.isEmpty()) {
            return new Applications.NoneHanded();
        }
        List<Applications.Made> applications = List.of(new Applications.Made(this, List.of()));
        for (int at = 0; at < handed.size(); at++) {
            List<Applications.Made> wider = new ArrayList<>();
            for (Applications.Made each : applications) {
                for (ReadMeaning.Occurrence occurrence : occurrencesOf.get(at)) {
                    List<ReadMeaning.Occurrence.Kept> keptBy = new ArrayList<>(each.keptWhere());
                    keptBy.addAll(occurrence.keptWhere());
                    wider.add(new Applications.Made(each.reads().handing(
                            handed.get(at).binding(), occurrence.value(), newtypes), keptBy));
                }
            }
            applications = wider;
        }
        long counted = readings;
        Map<BindingId, Long> through = new HashMap<>();
        for (int at = 0; at < handed.size(); at++) {
            through.put(handed.get(at).binding(), (long) occurrencesOf.get(at).size());
        }
        List<Applications.Made> each = applications.stream()
                .map(one -> new Applications.Made(one.reads().readAsApplication(counted, through),
                        one.keptWhere()))
                .toList();
        // An operation applying its closure to one element at most picks it out by something else
        // it was handed, and one applying it to some of them says not which; and applications made
        // of every value of each of several parameters are made in an order no operation here
        // states, so where one of them stops is not said either. Each is still an application a
        // run may make, and what it states on it is still what it states.
        if (how == HowAClosureIsApplied.AT_MOST_ONE || how == HowAClosureIsApplied.TO_SOME
                || (handed.size() > 1 && how != HowAClosureIsApplied.TO_EVERY_ELEMENT)) {
            return new Applications.Unsaid(each);
        }
        return new Applications.Each(each, how);
    }

    /**
     * The application of {@code block} that hands {@code value}, one of the values {@code container}
     * was written with, to the parameter {@code block}'s elements of it arrive on — or null where no
     * parameter of it takes the elements of {@code container}.
     *
     * <p>For a statement pairing an element of a container with what the closure answers of it: on
     * that application the parameter is that value, and a statement about the element is about the
     * same value.
     */
    public InputReads handingTheElement(Core.Block block, Core container, Denotation value,
                                        DeclarationNewtypes newtypes) {
        for (Core.Binder param : block.params()) {
            if (param != null && param.binding() != null
                    && names.roleOf(param.binding()) instanceof BindingRole.Element(var held)
                    && held.part() == HeldIn.Part.ELEMENT && held.container() == container) {
                return handing(param.binding(), value, newtypes);
            }
        }
        return null;
    }

    /**
     * The container {@code e} stands for an element of, where it is a parameter a walk hands each
     * element of one — or null where it is no such parameter.
     *
     * <p>Where a walk hands it elements of more than one container the parameter is none of them
     * in particular, and this says nothing about it.
     */
    public Core containerOfTheElement(Core e) {
        return Core.withoutStanding(e) instanceof Core.Read read && read.binding() != null
                ? containerOfTheElementHandedTo(read.binding()) : null;
    }

    /**
     * The containers the operations applying the closure {@code name} is a parameter of took what
     * it is handed from, whatever else the name stands for here: an element a fold was unrolled
     * over is a name for that element, and the container is what it was taken out of.
     */
    public List<Core> containersTheElementCameFrom(Core.Read name) {
        return names.handedFrom(name.binding()).stream().map(HeldIn::container).toList();
    }

    /** The same, of the parameter {@code binding} itself. */
    public Core containerOfTheElementHandedTo(BindingId binding) {
        return names.roleOf(binding) instanceof BindingRole.Element(var held)
                && held.part() == HeldIn.Part.ELEMENT ? held.container() : null;
    }

    /**
     * The same, for a rule a declaration states, which is the tree the analysis of that declaration
     * reads and keeps the language's operations standing as calls, whichever tree the value it is
     * handed is read in.
     */
    public InputReads forADeclaredRule() {
        return new InputReads(names.overStandingCalls(), alternatives, declared, dependencies,
                applied);
    }

    /** The same, as one of {@code readings} readings of one condition, the readings beyond the
     *  ones already made being the applications of a closure. */
    private InputReads readAsApplication(long readings, Map<BindingId, Long> through) {
        Map<BindingId, Long> widths = new HashMap<>(applied.widths());
        through.forEach((binding, width) -> widths.merge(binding, width, (a, b) -> a * b));
        return new InputReads(names, alternatives, declared, dependencies,
                new Applied(applied.handed(), readings, applied.taken(), applied.given(),
                        applied.picked(), applied.entered(), widths, applied.turnsOn()));
    }

    /**
     * How many readings of one condition a split of {@code values} is one of, when this is the
     * reading being split: the readings this one is, less the applications of closures through
     * parameters no value split reads.
     *
     * <p>A value that reads nothing a parameter was handed is the same value on each application
     * through it, so the cases it is split into are the same cases, and are split once for all of
     * them. One that reads a parameter is another value on each value that parameter is handed, and
     * is split with all of them, but not with the applications through a parameter of a closure
     * beside or inside that it does not read. What each of those adds is the comparison it makes in
     * one of those cases, which splits nothing.
     *
     * <p>The one place this is decided, so that a split cannot be counted the one way here and the
     * other where a sibling is: every split names the values it splits.
     *
     * @param values the values the split is of, each as it stands where it is read
     */
    public long readingsASplitIsOneOf(List<Denotation> values) {
        Set<BindingId> turnedOn = new HashSet<>();
        for (Denotation each : values) {
            each.at().applicationsRead(each.value(), new HashSet<>(), turnedOn);        }
        return applied.readings() / applied.applicationsNotThrough(turnedOn);
    }

    /**
     * The same, taking {@code node} as {@code as}, as one of {@code readings} readings for each this
     * one is.
     *
     * <p>Two things are taken as another value. A choice whose arm a reading is on: where a value
     * chosen by cases stands inside what is being read, what is read is read once for each arm, with
     * the choice standing for what that arm answers, and the readings are as many as the arms. And a
     * call of a behavior whose body a reading enters, which is that body read with the parameters
     * standing for what the call handed ({@link #calling}), one reading. Which arm a run takes is said
     * beside each reading by whoever split it; what is here is only that on this reading the node is
     * that value, wherever it is reached from — through a name, under an access, as an argument.
     */
    public InputReads taking(Core node, Denotation as, int readings) {
        return taking(node, new TakenAs.AValue(as), readings);
    }

    /**
     * The same, taking the call {@code node} as {@code form} of the values it was given: a case of
     * the definition an operation is written in, answering arithmetic over them.
     */
    public InputReads takingAForm(Core node, LinearForm<Core> form, int readings) {
        return taking(node, new TakenAs.AFormOfItsArguments(form), readings);
    }

    private InputReads taking(Core node, TakenAs as, int readings) {
        return new InputReads(names, alternatives, declared, dependencies,
                applied.as(applied.readings() * readings, applied.widths(),
                        new Taken(Core.withoutStanding(node), as, applied.taken())));
    }

    /**
     * What {@code e} is taken as on the reading here ({@link #taking}), where that is another
     * value — or null where it is not taken, or taken as a form of its arguments.
     */
    public Denotation taken(Core e) {
        // A build of a value is the value it is defined as on every reading, wherever it stands —
        // under a name or not ({@link #denoting}).
        Denotation defined = definedAs(e, this);
        if (defined != null) {
            return defined;
        }
        return applied.taken() == null
                || !(applied.taken().of(Core.withoutStanding(e)) instanceof TakenAs.AValue(var as))
                ? null : carryingWhatIsTaken(as);
    }

    /**
     * The form of the values it was given the call {@code e} is taken as on the reading here
     * ({@link #takingAForm}), or null where it is not taken as one.
     */
    public LinearForm<Core> takenAsAForm(Core e) {
        return applied.taken() == null
                || !(applied.taken().of(Core.withoutStanding(e))
                        instanceof TakenAs.AFormOfItsArguments(var form)) ? null : form;
    }

    /**
     * Whether a node stands for the same values here as it does in {@code other}: the names it
     * reads are bound to the same things. Readings made from one by taking a choice's arm or a
     * form stand in the same names; one an application or a call made stands in others.
     */
    public boolean standsInTheNamesOf(InputReads other) {
        return names.equals(other.names);
    }

    /** Whether {@code e} is taken as anything on the reading here, a value or a form. */
    public boolean isTaken(Core e) {
        return applied.taken() != null && applied.taken().of(Core.withoutStanding(e)) != null;
    }

    /**
     * What a name given {@code value} where {@code writtenAt} reads stands for, and what it is read
     * in.
     *
     * <p>The value as written, read there — except a build of a value, which stands for what the
     * value is defined as, read where a definition is read ({@link ValueDefinitions#reading}). A
     * definition names nothing of the place that builds it, so read in that place it would be read
     * under names it has nothing to do with, and in the tree that runs, in a representation that is
     * not its own. Which builds are builds is {@link ValueDefinitions#definitionOf}'s answer, and
     * every way a name is given a value comes through here, so a value is read alike however its name
     * was given it.
     *
     */
    private static Denotation denoting(Core value, InputReads writtenAt) {
        Denotation defined = definedAs(value, writtenAt);
        return defined != null ? defined : new Denotation(value, writtenAt);
    }

    /** What the build {@code value} written where {@code writtenAt} reads is defined as, read where
     *  a definition is — or null where it is no build. */
    private static Denotation definedAs(Core value, InputReads writtenAt) {
        ValueDefinitions values = writtenAt.names.values();
        Core definition = values.definitionOf(value);
        return definition == null ? null : new Denotation(definition, values.reading());
    }

    /**
     * {@code value}, read where it was given, with what this reading takes as another value taken so
     * there as well.
     *
     * <p>What a name was given is read in the reading it was given in, which knows nothing of what
     * was taken after; a value taken is the one value it was taken as wherever it is reached from,
     * so what this reading took goes with the value.
     */
    private Denotation carryingWhatIsTaken(Denotation value) {
        if (applied.taken() == null) {
            return value;
        }
        InputReads at = value.at();
        Taken taken = at.applied.taken() == null ? applied.taken()
                : at.applied.taken().under(applied.taken());
        // Carried already: the reading it stands in holds what this one took, and as many
        // readings. A reading made again would be one more value to hash wherever it is a key.
        if (taken == at.applied.taken() && applied.readings() == at.applied.readings()
                && applied.widths().equals(at.applied.widths())) {
            return value;
        }
        return new Denotation(value.value(), new InputReads(at.names, at.alternatives, at.declared,
                at.dependencies,
                at.applied.as(applied.readings(), applied.widths(), taken)));
    }

    /** The same, of an occurrence: its value and each thing it was kept by. */
    private ReadMeaning.Occurrence carryingWhatIsTaken(ReadMeaning.Occurrence occurrence) {
        return new ReadMeaning.Occurrence(carryingWhatIsTaken(occurrence.value()),
                occurrence.keptWhere().stream().map(this::carryingWhatIsTaken).toList(),
                occurrence.answered(), occurrence.within());
    }

    private ReadMeaning.Occurrence.Kept carryingWhatIsTaken(ReadMeaning.Occurrence.Kept kept) {
        return switch (kept) {
            case ReadMeaning.Occurrence.Kept.ATruth(Denotation truth, boolean holds,
                                                    OptionalInt application) ->
                    new ReadMeaning.Occurrence.Kept.ATruth(carryingWhatIsTaken(truth), holds,
                            application);
            case ReadMeaning.Occurrence.Kept.AnArm(Denotation fork, int part) ->
                    new ReadMeaning.Occurrence.Kept.AnArm(carryingWhatIsTaken(fork), part);
        };
    }

    /**
     * Where the body of {@code behavior}, called with {@code args} here, is read: its parameters
     * standing for what the call handed — a position where the argument stands at one, and the
     * argument read here where it does not — and what the body binds to the elements of what known
     * beside what this body does. The body is read as the tree its behavior's analysis reads,
     * where the language's operations stand as calls, whichever tree this reading is of ({@link
     * #calledWith}). Null where its body is entered already on the way here, which is
     * the behavior reached again while its own answer is being read, or where the call hands it
     * another number of values than it takes.
     *
     * <p>Nothing is stood in inside it. A row stands in the dependencies of the body it was written
     * for, and an evaluation inside the called body is one each call makes afresh, so what one of
     * them answers is no answer a row controls.
     */
    public InputReads calling(ValueName.Behavior behavior, CalledBody body, List<Core> args,
                              DeclarationNewtypes newtypes) {
        if (applied.entered().contains(behavior)) {
            return null;
        }
        Set<ValueName.Behavior> entered = new HashSet<>(applied.entered());
        entered.add(behavior);
        return calledWith(body, args, Map.of(), entered, newtypes);
    }

    /**
     * Where one step of a recursion over a list is read: the body a call of it names, with its
     * parameters standing for what the call handed as {@link #calling} has them, and {@code element}
     * standing at {@code at}, an element of the list the recursion walks — or null where the call
     * hands another number of values than the body takes.
     *
     * <p>What the step's own calls of the recursion answer is no binding here; a reader of the step
     * says what it takes them to answer.
     */
    public InputReads steppingThrough(CalledBody body, List<Core> args, BindingId element,
                                      TermPath at, DeclarationNewtypes newtypes) {
        return calledWith(body, args, Map.of(element, at), applied.entered(), newtypes);
    }

    /**
     * Where the body of a search from a node is read: the body a call of it names, with its
     * parameters standing for what the call handed as {@link #calling} has them — or null where the
     * call hands another number of values than the body takes.
     *
     * <p>What the body's own calls of the search answer is no binding here; a reader of the body
     * says what it takes them to answer.
     */
    public InputReads searching(CalledBody body, List<Core> args, DeclarationNewtypes newtypes) {
        return calledWith(body, args, Map.of(), applied.entered(), newtypes);
    }

    /**
     * Where {@code body} is read with what it binds known beside what this body does, each of
     * {@code standing} at its position, and its parameters standing for what a call handed it,
     * {@code entered} the bodies entered on the way — or null where the call hands another number
     * of values than the body takes. A parameter handed a value at a position stands at it, and
     * one handed anything else is given it as read here.
     *
     * <p>The body is the tree the analysis of its behavior reads, which keeps the language's
     * operations standing as calls whichever tree the call was read in; the arguments stay read
     * here.
     */
    private InputReads calledWith(CalledBody body, List<Core> args,
                                  Map<BindingId, TermPath> standing,
                                  Set<ValueName.Behavior> entered, DeclarationNewtypes newtypes) {
        if (args.size() != body.parameters().size()) {
            return null;
        }
        BindingEnvironment inside = names.entering(body.elements()).overStandingCalls();
        for (Map.Entry<BindingId, TermPath> each : standing.entrySet()) {
            inside = inside.naming(each.getKey(), each.getValue());
        }
        InputReads reading = new InputReads(inside, alternatives, declared,
                souther.compiler.carrier.Membership.none(),
                new Applied(applied.handed(), applied.readings(), applied.taken(),
                        applied.given(), applied.picked(), entered, applied.widths(),
                        applied.turnsOn()));
        for (int i = 0; i < args.size(); i++) {
            Core.Binder parameter = body.parameters().get(i);
            if (parameter == null || parameter.binding() == null) {
                continue;
            }
            reading = reading.standingFor(parameter.binding(),
                    new Denotation(args.get(i), this), newtypes);
        }
        // An element a step stands at is one of the list its call walks, which is among what the
        // call was handed.
        List<Denotation> handedOver = args.stream().map(each -> new Denotation(each, this)).toList();
        for (BindingId element : standing.keySet()) {
            reading = reading.turningOn(element, handedOver);
        }
        return reading;
    }

    /** Whether the body of {@code behavior} was entered on the way here ({@link #calling}). */
    public boolean entered(ValueName.Behavior behavior) {
        return applied.entered().contains(behavior);
    }

    /** Whether a reading here is inside the body of a behavior a call names ({@link #calling}). */
    public boolean insideACalledBody() {
        return !applied.entered().isEmpty();
    }

    /** What reading a closure's body on each of its applications comes to ({@link
     *  #applicationsOf}). */
    public sealed interface Applications {

        /**
         * One application: the names in force on it, and what has to hold of the values for the
         * container to hold the element it is handed — every truth the element was kept by, for
         * each parameter handed one ({@link ReadMeaning.Occurrence}). An application handed an
         * element a filter dropped is one no run makes.
         */
        record Made(InputReads reads, List<ReadMeaning.Occurrence.Kept> keptWhere) {

            public Made {
                Objects.requireNonNull(reads, "an application is read in some names");
                keptWhere = List.copyOf(keptWhere);
            }
        }

        /**
         * One application per occurrence, in the order a walk of the container meets them, which
         * is the order a run makes them in, and how far the operation goes making them.
         */
        record Each(List<Made> each, HowAClosureIsApplied how) implements Applications {

            public Each {
                each = List.copyOf(each);
                if (how == null) {
                    throw new IllegalArgumentException("applications are made some way");
                }
            }
        }

        /** No parameter is handed values written out: the body is read once, as it stands. */
        record NoneHanded() implements Applications {}

        /**
         * A parameter is handed the elements of a container that holds none on any row, so the
         * closure is applied to nothing and nothing in its body is reached.
         *
         * <p>Beside {@link NoneHanded} and the opposite of it. That one says which values the
         * closure is handed are not written out, and its body is read once as it stands because
         * some run may apply it to something; this one says no run applies it at all.
         */
        record NoneMade() implements Applications {}

        /**
         * One environment for each application a run may make, where which of them it makes is not
         * said: the operation applies its closure to one element at most, or to some of them, or
         * hands values to several parameters and stops.
         *
         * <p>What a condition states on each is said all the same, since that is a fact about the
         * application and not about whether a run makes it; where each is made among the others is
         * what is not.
         */
        record Unsaid(List<Made> each) implements Applications {

            public Unsaid {
                each = List.copyOf(each);
            }
        }

        /** More applications than a condition is read on, counting the ones this reading is
         *  already one of. */
        record MoreThanAreRead() implements Applications {}

        /**
         * A parameter is handed the elements of a container holding more than a walk writes out
         * ({@link ReadMeaning.MoreThanAreWrittenOut}), so the applications are not counted at all.
         *
         * <p>Beside {@link MoreThanAreRead} and not folded into it: the two stop at two figures,
         * and a reader told which is told the one that was reached.
         */
        record PastWhatIsWrittenOut() implements Applications {}
    }

    /** Whether {@code e} reads a binding it does not make itself. */
    private static boolean namesSomething(Core e) {
        Set<BindingId> made = new HashSet<>();
        Set<BindingId> read = new HashSet<>();
        walkNames(e, made, read);
        read.removeAll(made);
        return !read.isEmpty();
    }

    /**
     * The bindings {@code e} reads and the ones it makes. A binder this does not know of leaves the
     * name it makes read and not made, which says the value names something — the answer that hands
     * nothing, and never a wrong one.
     */
    private static void walkNames(Core e, Set<BindingId> made, Set<BindingId> read) {
        switch (e) {
            case Core.Read r -> read.add(r.binding());
            case Core.LetIn let -> madeBy(let.binder(), made);
            case Core.Block block -> block.params().forEach(each -> madeBy(each, made));
            case Core.Match match -> match.cases().forEach(arm -> madeBy(arm.binder(), made));
            case Core.IfConstructed fork -> madeBy(fork.binder(), made);
            default -> { }
        }
        Core.forEachChild(e, child -> walkNames(child, made, read));
    }

    private static void madeBy(Core.Binder binder, Set<BindingId> made) {
        if (binder != null && binder.binding() != null) {
            made.add(binder.binding());
        }
    }

    /** Whether a call to {@code behavior} is a value a row stands in for, read here. */
    public boolean standsIn(ValueName.Behavior behavior) {
        return dependencies.contains(behavior);
    }

    /**
     * Whether any value read here may be an answer of a dependency.
     *
     * <p>A body that stands nothing in has no answer anywhere in it, and the names it reads are not
     * walked to find that out — unless it is a body a call entered, whose parameters are read where
     * the call stands. Asked first by a reader that would otherwise do work to find an answer in a
     * body that has none.
     */
    public boolean mayHoldAnAnswer() {
        return !dependencies.isEmpty() || !applied.given().isEmpty();
    }

    /**
     * What a dependency answered that {@code e} is, at a place inside the answer — or null where
     * it is no such thing.
     *
     * <p>The one place a value is found to be an answer, and the only maker of an
     * {@link AnEvaluation}. Fields read off it are steps inside the answer; a name is the value it
     * was bound to only where its meaning is that value ({@link ReadMeaning.Through}), so
     * {@code let y = x} is the answer {@code x} is and {@code x + 1} is no answer at all. A field of
     * a newtype is the value it wraps and no step.
     *
     * @param e the value, in the tree {@code this} reads
     * @return the evaluation, the call written for it, where that call's arguments are read, and
     *         the fields read off the answer in the order they are written
     */
    public AnAnswerAt answerAt(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        if (!mayHoldAnAnswer()) {
            return null;
        }
        List<TermPath.Step> steps = new ArrayList<>();
        Core under = e;
        InputReads reads = this;
        while (true) {
            // Which answer a value is does not turn on the type it stands as.
            under = Core.withoutStanding(under);
            // The same accesses held as one node, taken a name at a time from the last.
            if (under instanceof Core.FieldProjection projection) {
                under = projection.lastAccess();
                continue;
            }
            if (under instanceof Core.FieldAccess field) {
                if (Location.isStep(field.target().type(), field.field(), newtypes)) {
                    steps.addFirst(new TermPath.Step.Field(field.field()));
                }
                under = field.target();
                continue;
            }
            // A name given the entry a lookup picked out of a map filed from an answer's list stands
            // at the element of that list, under the places the answer is.
            if (under instanceof Core.Read name && name.binding() != null
                    && reads.names.placeInAnAnswer(name.binding()) instanceof AnAnswerAt place) {
                return place.inside(steps);
            }
            if (under instanceof Core.Read name
                    && reads.meaningOf(name, symbols, newtypes) instanceof ReadMeaning.Through through) {
                under = through.denotes().value();
                reads = through.denotes().at();
                continue;
            }
            // What a walk hands each element of an answer is a place inside that answer: the
            // element, under the places the container is.
            if (under instanceof Core.Read element && reads.containerOfTheElement(element) != null) {
                AnAnswerAt container = reads.answerHoldingTheElementsOf(
                        reads.containerOfTheElement(element), symbols, newtypes);
                if (container == null) {
                    return null;
                }
                List<TermPath.Step> inside = new ArrayList<>();
                inside.add(new TermPath.Step.Element());
                inside.addAll(steps);
                return container.inside(inside);
            }
            break;
        }
        if (!(under instanceof Core.Call call && call.fn() instanceof Core.Reached reached
                && reached.denotes() instanceof ValueName.Behavior dependency
                && reads.standsIn(dependency))) {
            return null;
        }
        // A call inside one of the language's own operations is none the model writes.
        Optional<ModelOccurrence> written = ModelOccurrence.statedAt(call.occurrence());
        return written.isEmpty() ? null : new AnAnswerAt(
                new AnEvaluation(dependency, written.get()), call.args(), reads, steps);
    }

    /**
     * The answer of a dependency whose very elements {@code container} holds, or null where it holds
     * none's.
     *
     * <p>Through the operations that answer the elements of what they were given — a reordered list,
     * a filtered one — as a walk to the position an element stands at goes through them
     * ({@link InputPath#argumentWhoseElementsItHolds}), so an element of either is where it was
     * whether the list it came from is a position of the input or an answer.
     */
    private AnAnswerAt answerHoldingTheElementsOf(Core container, Symbols symbols,
                                                  DeclarationNewtypes newtypes) {
        Denotation at = standing(container, symbols, newtypes);
        while (true) {
            AnAnswerAt found = at.at().answerAt(at.value(), symbols, newtypes);
            if (found != null) {
                return found;
            }
            at = oneStepBeneath(at, symbols, newtypes, (operation, args, where) ->
                    holdingTheElementsOf(operation, args, where, symbols, newtypes));
            if (at == null) {
                return null;
            }
        }
    }

    /**
     * The argument whose very elements {@code operation}, applied to {@code args}, answers some of:
     * the one its law says it holds the elements of — a filter, a reordering — or the one a closure
     * answering each element as it is was handed. Null where it answers no argument's.
     *
     * <p>The one step down a list to the list its elements are the elements of, for every reader
     * that follows an element back to where it was handed from.
     */
    private static DeclaredArgument holdingTheElementsOf(ValueName operation, List<Core> args,
                                                         InputReads where, Symbols symbols,
                                                         DeclarationNewtypes newtypes) {
        DeclaredArgument holds = InputPath.argumentWhoseElementsItHolds(operation);
        return holds != null ? holds
                : keepingEveryElement(operation, args, where, symbols, newtypes);
    }

    /**
     * The answer of a dependency whose every element {@code container} holds, each as often, or
     * null where it holds none's.
     *
     * <p>Only through the operations that keep every element ({@link #stepKeepingEveryElement}): a
     * filtered list holds some of the elements of the answer, and what is added up over those is
     * added up over no element of it.
     */
    public AnAnswerAt answerWhoseEveryElementIsHeldBy(Core container, Symbols symbols,
                                                      DeclarationNewtypes newtypes) {
        Denotation at = standing(container, symbols, newtypes);
        while (at != null) {
            AnAnswerAt found = at.at().answerAt(at.value(), symbols, newtypes);
            if (found != null) {
                return found;
            }
            at = stepKeepingEveryElement(at, symbols, newtypes);
        }
        return null;
    }

    /**
     * The answer of a dependency whose elements {@code container} holds, once each, and the
     * direction it holds them in: the order the answer lists them or the opposite. Null where
     * {@code container} is no such answer.
     *
     * <p>Beside {@link #answerWhoseEveryElementIsHeldBy} and stronger again, as the input's
     * {@link InputPath#inTheOrderAt} is beside its everyElementAt. The only operations crossed are
     * those declared to answer a list the other way round, each turning the direction over; one that
     * puts the elements in any other order, or answers each as it is, says nothing of the order and
     * the walk stops at it.
     */
    public AnAnswerInOrder answerHandedInOrder(Core container, Symbols symbols,
                                               DeclarationNewtypes newtypes) {
        Denotation at = standing(container, symbols, newtypes);
        TraversalDirection direction = TraversalDirection.FORWARD;
        while (at != null) {
            AnAnswerAt found = at.at().answerAt(at.value(), symbols, newtypes);
            if (found != null) {
                return new AnAnswerInOrder(found, direction);
            }
            if (!(applicationIn(at.value()) instanceof Application(var operation, var args))) {
                return null;
            }
            int reversed = DefaultBoundOperationFacts.positionOfTheArgumentReversed(operation);
            if (reversed < 0 || reversed >= args.size()) {
                return null;
            }
            direction = direction.reversed();
            at = at.at().standing(args.get(reversed), symbols, newtypes);
        }
        return null;
    }

    /** What {@link #answerHandedInOrder} found: the answer, and the direction its elements are
     *  handed in relative to the order it lists them. */
    public record AnAnswerInOrder(AnAnswerAt answer, TraversalDirection direction) {

        public AnAnswerInOrder {
            if (answer == null || direction == null) {
                throw new IllegalArgumentException("elements in an order are those of some answer,"
                        + " handed in some direction");
            }
        }
    }

    /** An operation and the arguments it was applied to. */
    private record Application(ValueName operation, List<Core> args) {}

    private static Application applicationIn(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Call call when call.fn() instanceof Core.Reached reached ->
                    new Application(reached.denotes(), call.args());
            case Core.PreservedCall kept ->
                    new Application(kept.declared().operation(), kept.args());
            default -> null;
        };
    }

    /**
     * The list {@code at} is the answer of an operation that keeps every element of, each as often
     * — one it puts in another order, or the one a closure that answers each element as it is was
     * handed — standing where it is read, or null where {@code at} is no such answer.
     */
    public Denotation stepKeepingEveryElement(Denotation at, Symbols symbols,
                                              DeclarationNewtypes newtypes) {
        return oneStepBeneath(at, symbols, newtypes, (operation, args, where) ->
                keepingEveryElement(operation, args, where, symbols, newtypes));
    }

    private static DeclaredArgument keepingEveryElement(ValueName operation, List<Core> args,
                                                        InputReads where, Symbols symbols,
                                                        DeclarationNewtypes newtypes) {
        return InputPath.argumentKeepingEveryElement(operation, args,
                closure -> Core.withoutStanding(where.standing(closure, symbols, newtypes).value())
                        instanceof Core.Block block ? block : null,
                where.heldByTheBody(), newtypes);
    }

    /** Which argument of an operation applied to {@code args} a step goes down to. */
    private interface Crossed {
        DeclaredArgument of(ValueName operation, List<Core> args, InputReads where);
    }

    private Denotation oneStepBeneath(Denotation at, Symbols symbols, DeclarationNewtypes newtypes,
                                      Crossed crossed) {
        ValueName operation;
        List<Core> args;
        switch (Core.withoutStanding(at.value())) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return null;
            }
        }
        DeclaredArgument holds = crossed.of(operation, args, at.at());
        int position = holds == null ? -1 : CallArguments.positionOf(holds, operation);
        return position < 0 || position >= args.size() ? null
                : at.at().standing(args.get(position), symbols, newtypes);
    }

    /**
     * What {@link #answerAt} found.
     *
     * @param evaluation which evaluation of which dependency
     * @param arguments  what the call written for it hands the dependency
     * @param at         where those arguments are read
     * @param steps      the fields read off the answer, in the order they are written
     */
    public record AnAnswerAt(AnEvaluation evaluation, List<Core> arguments, InputReads at,
                             List<TermPath.Step> steps) {

        public AnAnswerAt {
            if (evaluation == null || arguments == null || at == null || steps == null) {
                throw new IllegalArgumentException("an answer found is some evaluation, handed"
                        + " something read somewhere, at some place inside it");
            }
            arguments = List.copyOf(arguments);
            steps = List.copyOf(steps);
        }

        /** The same answer, at the place {@code further} leads to from this one. */
        public AnAnswerAt inside(List<TermPath.Step> further) {
            List<TermPath.Step> all = new ArrayList<>(steps);
            all.addAll(further);
            return new AnAnswerAt(evaluation, arguments, at, all);
        }
    }

    /**
     * The same, inside one arm of a {@code match} over {@code scrutinee}.
     *
     * <p>A name an arm binds stands for the value that was matched, read as the case the arm
     * selects — which is the position the scrutinee is at, narrowed. Written here and nowhere else:
     * every walk that goes into an arm meets the same binder, and each working out for itself what
     * it names is as many spellings of one position as there are walks, of which the axes carry
     * one.
     *
     * <p>Where the arm narrows the scrutinee, to one of its distinctions or to several: an arm naming
     * a case that is itself a sum, or naming several cases, leaves the value the leaves they cover,
     * and the name stands at the position narrowed to those. Where the declaration already leaves
     * the value nothing the arm does not cover, the arm narrows nothing and the name stands at the
     * position as it is.
     *
     * <p><b>And the narrowing is the checker's resolution, not one worked out from it here.</b>
     * Which case an arm took was decided there, together with what the value turns out to be once
     * it is taken and which leaves selecting it covers; a reader that took the case's name instead
     * would have an optional's present carrier and a sum's case declared under the same word
     * arriving as one thing, and a case above two leaves arriving as a place. So what crosses into
     * this vocabulary is the resolved selection, whole. The scrutinee's type is handed on with it and
     * decides nothing about the case: it says which of the names a value wears the arm can be
     * matching ({@link DeclaredInput#taking}).
     *
     * <p><b>And where the scrutinee stands for one of several written values, the arm narrows that
     * set.</b> Which is a different answer from the one above and not a weaker copy of it: a
     * position is one place a row writes at, and a set is every value the name can take. An arm
     * admitting one case takes out the members that are not of it and leaves the rest — however
     * many that is. A container written with two members of the admitted case leaves two, and an
     * arm is no evidence that the name is one of them: what would make it one is there being one
     * left, which is what the set says and the arm does not.
     *
     * <p>Reached through {@link #choosing} and from nowhere else, so that a walk going into an arm
     * says which way of deciding took it there rather than which node it is standing on.
     */
    private InputReads insideArmOn(Core scrutinee, Core.Case arm, Symbols symbols,
                                   DeclarationNewtypes newtypes) {
        InputReads inside = narrowedInsideArmOn(scrutinee, arm, symbols, newtypes);
        if (arm.binder() == null || arm.binder().binding() == null
                || !(arm.binding() instanceof Core.ArmBinding.Payload)) {
            return inside;
        }
        // A call is the lookup itself; only a name for one is followed to it.
        Core written = Core.withoutStanding(scrutinee);
        Core lookup = written instanceof Core.Read
                ? standing(scrutinee, symbols, newtypes).value() : written;
        return AnOperationApplied.of(lookup) instanceof AnOperationApplied looked
                && GET.equals(looked.operation())
                ? new InputReads(inside.names.opening(arm.binder().binding(),
                        new LookupOpened(lookup, new EnteredArm(arm.binder().binding()))),
                        inside.alternatives, inside.declared, inside.dependencies, inside.applied)
                : inside;
    }

    /**
     * What a name under an arm is the value of: the lookup in a map that found it under its key,
     * and which arm is reached only where the lookup found one.
     *
     * @param lookup  the call that asked the map for the key, itself and not one like it
     * @param entered the arm that binds the name
     */
    public record LookupOpened(Core lookup, EnteredArm entered) {

        public LookupOpened {
            Objects.requireNonNull(lookup, "a name is found by some lookup");
            Objects.requireNonNull(entered, "under some arm of the match on it");
        }

        /** The same arm: the name it binds is of one lookup, and the call read through the names
         *  in force is a new tree each time it is read, which would tell equal readings apart. */
        @Override
        public boolean equals(Object other) {
            return other instanceof LookupOpened that && entered.equals(that.entered);
        }

        @Override
        public int hashCode() {
            return entered.hashCode();
        }
    }

    /** What the name {@code binding} is the value of, where an arm bound it to what a lookup in a
     *  map found under its key — or null where it is no such name. */
    public LookupOpened lookupOpenedBy(BindingId binding) {
        return names.openedBy(binding);
    }

    /** {@link #insideArmOn}, without the lookup the name under the arm is found by. */
    private InputReads narrowedInsideArmOn(Core scrutinee, Core.Case arm, Symbols symbols,
                                           DeclarationNewtypes newtypes) {
        if (arm.binder() == null || arm.binder().binding() == null) {
            return this;
        }
        return namedByTheArm(scrutinee, arm, symbols, newtypes)
                .turningOn(arm.binder().binding(), List.of(new Denotation(scrutinee, this)));
    }

    private InputReads namedByTheArm(Core scrutinee, Core.Case arm, Symbols symbols,
                                     DeclarationNewtypes newtypes) {
        if (arm.binding() instanceof Core.ArmBinding.Payload) {
            WhatItHolds held = whatItHolds(scrutinee, symbols, newtypes);
            // Which element an index picks is said beside whatever the arm narrows the name to:
            // a list of the input's own elements has the name stand at them as well.
            if (held instanceof WhatItHolds.AtAnIndex(PickedAtAnIndex element)) {
                return picking(arm.binder().binding(), element)
                        .narrowedByThePattern(scrutinee, arm, symbols, newtypes);
            }
            InputReads holding = holdingWhatItHolds(held, arm.binder(), newtypes);
            if (holding != null) {
                return holding;
            }
        }
        return narrowedByThePattern(scrutinee, arm, symbols, newtypes);
    }

    /** {@link #narrowedInsideArmOn}, where what the arm's name is is what its pattern narrows the
     *  scrutinee to. */
    private InputReads narrowedByThePattern(Core scrutinee, Core.Case arm, Symbols symbols,
                                            DeclarationNewtypes newtypes) {
        // An arm over an optional's two carriers at once leaves a position nothing to narrow it to.
        CasesLeft selected = CasesLeft.selectedBy(arm.pattern());
        if (selected == null) {
            return admitting(scrutinee, arm, symbols, newtypes);
        }
        // What the arm narrows is a position of the input, and a scrutinee that stands at none
        // narrows nothing.
        TermPath standing = switch (forkedOn(scrutinee, newtypes)) {
            case PathResolution.At(var at) -> at;
            case PathResolution.NotAPosition _ -> null;
            // A scrutinee that only may stand at a position narrows nothing here either. What an
            // arm narrows is one position, and narrowing each of the ones it may be would say a
            // value under this arm is a case of every one of them at once.
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> null;
        };
        if (standing == null) {
            return admitting(scrutinee, arm, symbols, newtypes);
        }
        // The case is relative to the type the scrutinee stands as here, and the value may have been
        // handed in as a wider one than it is. What the declaration puts at the position says
        // whether the arm narrows it, finds it already the case, or finds it never one.
        TermPath narrowed = switch (declared.taking(standing, scrutinee.type(), selected)) {
            case DeclaredInput.Taking.Narrows(TermPath to) -> to;
            case DeclaredInput.Taking.Implied _ -> standing;
            // No value at the position is of the case, so the name under the arm stands at no
            // position of it.
            case DeclaredInput.Taking.Excluded _ -> null;
        };
        if (narrowed == null) {
            return admitting(scrutinee, arm, symbols, newtypes);
        }
        // And nothing is asked of the reading. What this answers is which location the arm's name
        // stands for, which the arm, the scrutinee's path and the declaration settle between them:
        // the value that was matched, read as the case the arm selects. Whether a row is ever
        // written there — whether the position exists, whether the rules leave the case anything —
        // is a question about the model, and it is {@link InputDomain}'s to answer about the path
        // this produced.
        //
        // Held together, the two could not both be answered: the reading has to be built before it
        // can be asked, and it cannot be built without knowing which paths the body names. Asking
        // only the first here is what breaks that circle, and the cost of asking it alone is a name
        // that stands for a place no row reaches — which the reading refuses when it is asked.
        return new InputReads(names.naming(arm.binder().binding(), narrowed), alternatives,
                declared, dependencies, applied);
    }

    /**
     * Whether what {@code option} holds is made of an entry of the input's map that a lookup
     * answered: the lookup's own answer, or an option made of it by an operation answering its
     * closure on what an option holds. An arm opening it is about that entry.
     *
     * <p>Which entry an arm is about, and not what the name under it is. A name opening the
     * lookup itself stands at the map's elements; one opening what a closure made of the entry's
     * value stands for what the closure made, and the entry is only what it was made of. Either
     * way what the arm states is about the entry whose key was asked for, which is what the
     * proposition over the arm says. Asked of the option and not of each arm, since it is the
     * same answer for every arm that opens it.
     */
    public boolean holdsAnEntryLookedUp(Core option, Symbols symbols,
                                        DeclarationNewtypes newtypes) {
        return whatItHolds(option, symbols, newtypes).madeOf() != null;
    }

    /**
     * Whether what {@code option} holds is an entry that a lookup answered in a map filed from the
     * list a dependency answered ({@link WhatItHolds.AnEntryOfAnAnswer}): whether the option holds
     * one is a fact about what the dependency answered.
     */
    public boolean holdsAnEntryOfAnAnswer(Core option, Symbols symbols,
                                          DeclarationNewtypes newtypes) {
        return mayHoldAnAnswer()
                && whatItHolds(option, symbols, newtypes) instanceof WhatItHolds.AnEntryOfAnAnswer;
    }

    /**
     * What a value an option holds is, said so that a name in any reading can be bound to it.
     *
     * <p>Worked out in the reading the option stands in, which is not this one wherever the option
     * was reached through a binding or a call; and carried back as a position, which every reading
     * spells alike, or as a value together with the reading it is read in. Bound in that form
     * ({@link #holding}), a name stands for the same value wherever it is read, and nothing here
     * asks whether two readings are the same object.
     */
    sealed interface WhatItHolds {

        /** The entry a lookup picked out, whose value it is. Null where it was made of none. */
        EntryLookedUp madeOf();

        /** The value of the entry under the key. */
        record AnEntry(EntryLookedUp entry) implements WhatItHolds {

            public AnEntry {
                Objects.requireNonNull(entry, "an entry some lookup picked out");
            }

            @Override
            public EntryLookedUp madeOf() {
                return entry;
            }
        }

        /** The value of the entry under the key in a map filed from the list a dependency
         *  answered: the list's element, at its place inside the answer. */
        record AnEntryOfAnAnswer(AnAnswerAt place) implements WhatItHolds {

            public AnEntryOfAnAnswer {
                Objects.requireNonNull(place, "some place inside an answer");
            }

            @Override
            public EntryLookedUp madeOf() {
                return null;
            }
        }

        /** The value at a position of the input: an optional's, narrowed to its value. */
        record AtAPosition(TermPath at) implements WhatItHolds {

            public AtAPosition {
                Objects.requireNonNull(at, "some position");
            }

            @Override
            public EntryLookedUp madeOf() {
                return null;
            }
        }

        /**
         * What a closure answered on the value another option holds: its body, read where its
         * parameter stands for that value, and what that value is — which says the entry it was
         * made of, where it was made of one.
         */
        record MadeByAClosure(Denotation answered, WhatItHolds handed) implements WhatItHolds {

            public MadeByAClosure {
                Objects.requireNonNull(answered, "what the closure answered is read somewhere");
                Objects.requireNonNull(handed, "and it was handed some value, said or not");
            }

            @Override
            public EntryLookedUp madeOf() {
                return handed.madeOf();
            }
        }

        /**
         * The element an index written down picks of a list written out
         * ({@link ElementsWrittenOut#picked}) — a list written in the source, the code points of a
         * text written there, or one an operation put together of pieces of either — read where
         * the walk wrote it. Made of no entry: the list is no map, and the element is what it was
         * before it was put in.
         */
        record AnElement(Denotation element) implements WhatItHolds {

            public AnElement {
                Objects.requireNonNull(element, "the element the index picks");
            }

            @Override
            public EntryLookedUp madeOf() {
                return null;
            }
        }

        /**
         * The element at an index written down of a list no walk writes out: which element that is
         * turns on what the list is, which a reader of numbers follows through the operations that
         * made it. Made of no entry, as a list's element is not.
         */
        record AtAnIndex(PickedAtAnIndex picked) implements WhatItHolds {

            public AtAnIndex {
                Objects.requireNonNull(picked, "an element some index picks");
            }

            @Override
            public EntryLookedUp madeOf() {
                return null;
            }
        }

        /** Nothing says. */
        record Unsaid() implements WhatItHolds {

            @Override
            public EntryLookedUp madeOf() {
                return null;
            }
        }
    }

    /**
     * What {@code option}, read here, holds where it holds a value ({@link WhatItHolds}).
     *
     * <p>Followed by {@link WhatAnOptionHolds}, which the discharge of a rule follows as well: a
     * lookup in a list written out holds the element its index picks, and an operation answering
     * its closure on what another option holds holds the closure's answer on that. What only an
     * input has is answered here: a lookup in the input's map holds the entry under the key, and an
     * optional at a position holds what stands there.
     */
    WhatItHolds whatItHolds(Core option, Symbols symbols, DeclarationNewtypes newtypes) {
        return WhatAnOptionHolds.of(option, this, new Holds(symbols, newtypes));
    }

    /**
     * How {@link WhatAnOptionHolds} reads an option here: names followed by this reading, a
     * closure's parameter standing for what it is handed ({@link #holding}), and what only an input
     * has answered here — the entry a lookup in the input's map picks, and what stands at a position
     * of the input.
     */
    private record Holds(Symbols symbols, DeclarationNewtypes newtypes)
            implements WhatAnOptionHolds.Reading<InputReads, WhatItHolds> {

        Holds {
            Objects.requireNonNull(symbols, "names are followed against some library");
            Objects.requireNonNull(newtypes, "and some declarations' newtypes");
        }

        @Override
        public ElementsWrittenOut.Stood<InputReads> standing(Core e, InputReads at) {
            Denotation stood = at.standing(e, symbols, newtypes);
            return new ElementsWrittenOut.Stood<>(stood.value(), stood.at());
        }

        @Override
        public InputReads handing(InputReads at, BindingId element,
                                  ElementsWrittenOut.Stood<InputReads> value) {
            return at.handing(element, new Denotation(value.value(), value.at()), newtypes);
        }

        @Override
        public InputReads choosing(InputReads at, Choice.Decides decidedBy) {
            return at.choosing(decidedBy, symbols, newtypes);
        }

        @Override
        public Optional<Object> folded(ElementsWrittenOut.Stood<InputReads> value) {
            return value.at().folded(value.value(), symbols, newtypes);
        }

        @Override
        public WhatItHolds anElement(ElementsWrittenOut.Stood<InputReads> element) {
            return new WhatItHolds.AnElement(new Denotation(element.value(), element.at()));
        }

        @Override
        public WhatItHolds madeByAClosure(ElementsWrittenOut.Stood<InputReads> answered,
                                          WhatItHolds handed) {
            return new WhatItHolds.MadeByAClosure(new Denotation(answered.value(), answered.at()),
                    handed);
        }

        @Override
        public InputReads holding(InputReads at, BindingId parameter, WhatItHolds handed) {
            return at.holding(parameter, handed, newtypes);
        }

        @Override
        public WhatItHolds otherwise(ElementsWrittenOut.Stood<InputReads> option,
                                     AnOperationApplied applied) {
            InputReads at = option.at();
            if (applied != null && applied.operation() instanceof ValueName.Stdlib.Operation listed
                    && symbols.kernelOf(listed) == Kernel.LIST_GET) {
                return applied.args().size() == 2
                        && at.folded(applied.args().get(0), symbols, newtypes).orElse(null)
                                instanceof Long index && index >= 0
                        ? new WhatItHolds.AtAnIndex(new PickedAtAnIndex(
                                new Denotation(applied.args().get(1), at), index))
                        : unsaid();
            }
            if (applied != null) {
                if (!GET.equals(applied.operation()) || applied.args().size() != 2) {
                    return unsaid();
                }
                EntryLookedUp entry = at.entryLookedUp(new Denotation(option.value(), at),
                        applied.args(), symbols, newtypes);
                if (entry != null) {
                    return new WhatItHolds.AnEntry(entry);
                }
                AnAnswerAt held = at.mayHoldAnAnswer()
                        ? at.entryOfAnAnswer(applied.args(), symbols, newtypes) : null;
                return held == null ? unsaid() : new WhatItHolds.AnEntryOfAnAnswer(held);
            }
            // An optional at a position holds what stands there narrowed to its present case.
            if (!(at.forkedOn(option.value(), newtypes)
                    instanceof PathResolution.At(TermPath path))) {
                return unsaid();
            }
            TermPath narrowed = switch (at.declared.taking(path, option.value().type(), PRESENT)) {
                case DeclaredInput.Taking.Narrows(TermPath to) -> to;
                case DeclaredInput.Taking.Implied _ -> path;
                case DeclaredInput.Taking.Excluded _ -> null;
            };
            return narrowed == null ? unsaid() : new WhatItHolds.AtAPosition(narrowed);
        }

        @Override
        public WhatItHolds unsaid() {
            return new WhatItHolds.Unsaid();
        }
    }

    /**
     * This reading, with {@code name} standing for {@code held}: at the entry's element and read
     * of that entry, at the position, or for what the closure answered, read where it was — or as
     * it was, where nothing is said.
     *
     * <p>A value read where it was is handed as a call hands a parameter what it was given
     * ({@link #calledWith}): a position where it stands at one, which every reading spells alike,
     * and otherwise the value read there, in the reading its names are bound in, which a binding
     * made here would not have.
     */
    private InputReads holding(BindingId name, WhatItHolds held, DeclarationNewtypes newtypes) {
        return switch (held) {
            case WhatItHolds.AnEntry(EntryLookedUp entry) -> new InputReads(
                    names.naming(name, entry.element()).selecting(name, entry), alternatives,
                    declared, dependencies, applied)
                    .turningOn(name, List.of(new Denotation(entry.lookup(), this)));
            case WhatItHolds.AtAPosition(TermPath at) -> new InputReads(names.naming(name, at),
                    alternatives, declared, dependencies, applied);
            case WhatItHolds.AnEntryOfAnAnswer(AnAnswerAt place) -> new InputReads(
                    names.namingAPlaceInAnAnswer(name, place), alternatives, declared, dependencies,
                    applied).turningOn(name, place.arguments().stream()
                            .map(each -> new Denotation(each, place.at())).toList());
            case WhatItHolds.MadeByAClosure(Denotation answered, var _) ->
                    standingFor(name, answered, newtypes);
            case WhatItHolds.AnElement(Denotation element) -> standingFor(name, element, newtypes);
            case WhatItHolds.AtAnIndex(PickedAtAnIndex element) -> picking(name, element);
            case WhatItHolds.Unsaid _ -> this;
        };
    }

    /** This reading, with {@code name} standing for the element an index picks of a list as
     *  well as for whatever else it stands for. */
    private InputReads picking(BindingId name, PickedAtAnIndex element) {
        Map<BindingId, PickedAtAnIndex> picked = new LinkedHashMap<>(applied.picked());
        picked.put(name, element);
        return new InputReads(names, alternatives, declared, dependencies,
                new Applied(applied.handed(), applied.readings(), applied.taken(),
                        applied.given(), picked, applied.entered(), applied.widths(),
                        applied.turnsOn()));
    }

    /**
     * The element an index written down picks of a list, which a name an arm opening the lookup
     * bound stands for.
     *
     * @param list  the list, read where the lookup stands
     * @param index the index written down
     */
    public record PickedAtAnIndex(Denotation list, long index) {

        public PickedAtAnIndex {
            Objects.requireNonNull(list, "an element of some list");
        }
    }

    /**
     * The element of a list at an index written down that {@code e} stands for, where it is a name
     * an arm opening that lookup bound ({@link WhatItHolds.AtAnIndex}) — or null.
     */
    public PickedAtAnIndex pickedAtAnIndex(Core e) {
        return Core.withoutStanding(e) instanceof Core.Read read
                ? applied.picked().get(read.binding()) : null;
    }

    /**
     * This reading, with {@code name} standing for {@code value}: at its position where it stands
     * at one, and otherwise for the value read where it was.
     *
     * <p>The one place a name is given a value, by a call handing a parameter an argument or an
     * arm binding what it holds. Which parameters of the applications on the way down the value
     * reads is said here, where the value is in hand: a name at a position keeps no trace of the
     * value it was given, and the position does not say which application chose it.
     */
    private InputReads standingFor(BindingId name, Denotation value,
                                   DeclarationNewtypes newtypes) {
        if (value.at().pathOf(value.value(), newtypes) instanceof PathResolution.At(TermPath at)) {
            return new InputReads(names.naming(name, at), alternatives, declared, dependencies,
                    applied).turningOn(name, List.of(value));
        }
        Map<BindingId, Denotation> given = new LinkedHashMap<>(applied.given());
        given.put(name, value);
        return new InputReads(names, alternatives, declared, dependencies,
                new Applied(applied.handed(), applied.readings(), applied.taken(), given,
                        applied.picked(), applied.entered(), applied.widths(), applied.turnsOn()))
                .turningOn(name, List.of(value));
    }

    /**
     * This reading, with {@code name} known to turn on the parameters applications on the way down
     * handed values that {@code values}, the ones it was given or found by, read.
     *
     * <p>Said wherever a name is given a position, and only there: a position is the same
     * whichever application chose it, and what the name was found by is the one place that
     * is not.
     */
    private InputReads turningOn(BindingId name, List<Denotation> values) {
        Set<BindingId> reads = new HashSet<>();
        for (Denotation each : values) {
            if (!each.at().applied.handed().isEmpty()) {
                each.at().applicationsRead(each.value(), new HashSet<>(), reads);
            }
        }
        if (reads.isEmpty()) {
            return this;
        }
        Map<BindingId, Set<BindingId>> turnsOn = new HashMap<>(applied.turnsOn());
        turnsOn.merge(name, Set.copyOf(reads), (before, now) -> {
            Set<BindingId> both = new HashSet<>(before);
            both.addAll(now);
            return Set.copyOf(both);
        });
        return new InputReads(names, alternatives, declared, dependencies,
                new Applied(applied.handed(), applied.readings(), applied.taken(), applied.given(),
                        applied.picked(), applied.entered(), applied.widths(), turnsOn));
    }

    /**
     * This reading inside an arm opening {@code option}, with {@code name} standing for what it
     * holds — or null where no lookup, closure or written-out list says what that is, and what the
     * arm narrows a position to is left to say it.
     *
     * <p>What a lookup in the input's map answered is the value of the entry under the key: the
     * name stands at the map's elements, and is read of that entry and no other. What an operation
     * answering its closure on what another option holds holds is the closure's answer on that
     * one's value, so the value is never the entry's own: under
     * {@code Option.map(x -> x + 1, Map.get(k, m))} the name is the entry's value and one more,
     * and which entry it was made of is said apart from it ({@link #holdsAnEntryLookedUp}).
     */
    private InputReads holdingWhatItHolds(WhatItHolds held, Core.Binder name,
                                          DeclarationNewtypes newtypes) {
        return switch (held) {
            case WhatItHolds.AnEntry _, WhatItHolds.AnEntryOfAnAnswer _,
                 WhatItHolds.MadeByAClosure _, WhatItHolds.AnElement _ ->
                    holding(name.binding(), held, newtypes);
            case WhatItHolds.AtAPosition _, WhatItHolds.AtAnIndex _, WhatItHolds.Unsaid _ -> null;
        };
    }

    /**
     * Where an entry a lookup answered stands, and the lookup that picked it out.
     *
     * @param element where the entry's value stands: the element of the map or of the list the
     *                map was filed from
     * @param lookup  the call that asked for the key, as the tree has it
     */
    public record EntryLookedUp(TermPath element, Core lookup) {

        public EntryLookedUp {
            Objects.requireNonNull(element, "an entry's value stands at some element");
            Objects.requireNonNull(lookup, "an entry was picked out by some lookup");
        }
    }

    /** The entry the lookup {@code looked}, handed {@code args}, picks out of a map of the input —
     *  or null where the map is none. */
    private EntryLookedUp entryLookedUp(Denotation looked, List<Core> args, Symbols symbols,
                                        DeclarationNewtypes newtypes) {
        if (looked.at().forkedOn(args.get(1), newtypes) instanceof PathResolution.At(
                TermPath map)) {
            return new EntryLookedUp(map.element(), looked.value());
        }
        // A map filed from a list holds the list's own elements, so what a lookup in it answers is
        // one of them.
        Denotation held = looked.at().standing(args.get(1), symbols, newtypes);
        AnIndexedMap indexed = AnIndexedMap.of(held.value(), closure ->
                Core.withoutStanding(held.at().standing(closure, symbols, newtypes).value())
                        instanceof Core.Block block ? block : null);
        if (indexed == null) {
            return null;
        }
        Denotation walked = held.at().standing(indexed.walked(), symbols, newtypes);
        return walked.at().forkedOn(walked.value(), newtypes) instanceof PathResolution.At(
                TermPath list) ? new EntryLookedUp(list.element(), looked.value()) : null;
    }

    /**
     * Where the entry a lookup in a map filed from the list a dependency answered picks out
     * stands: the list's element, inside the answer — or null where the map is none.
     *
     * <p>The list itself, as it stands in the answer: a list the map was filed from through steps
     * that keep only some of its elements holds entries the answer's list does not.
     */
    private AnAnswerAt entryOfAnAnswer(List<Core> args, Symbols symbols,
                                       DeclarationNewtypes newtypes) {
        Denotation held = standing(args.get(1), symbols, newtypes);
        AnIndexedMap indexed = AnIndexedMap.of(held.value(), closure ->
                Core.withoutStanding(held.at().standing(closure, symbols, newtypes).value())
                        instanceof Core.Block block ? block : null);
        if (indexed == null) {
            return null;
        }
        Denotation walked = held.at().standing(indexed.walked(), symbols, newtypes);
        AnAnswerAt list = walked.at().answerAt(walked.value(), symbols, newtypes);
        if (list == null) {
            return null;
        }
        return list.inside(List.of(new TermPath.Step.Element()));
    }

    /**
     * Which part of which container a name is the element of, and the name that was given it.
     *
     * @param name      the binding that was handed the element, which is not an alias of another
     * @param container the container it is held in: by its position where it has one, and by what
     *                  it is made of otherwise, so that the elements of what a walk answered are
     *                  not the elements of what the walk was given
     * @param part      whether the name is the element or the key of its entry
     */
    record ElementStood(BindingId name, ContainerOf container, HeldIn.Part part) {

        ElementStood {
            Objects.requireNonNull(name, "an element is stood for by some name");
            Objects.requireNonNull(container, "an element is held in some container");
            Objects.requireNonNull(part, "an element is the element or the key of its entry");
        }
    }

    /** The container an element is held in. */
    sealed interface ContainerOf {

        /** One that stands at a position of the input. */
        record AtAPosition(TermPath at) implements ContainerOf {

            public AtAPosition {
                Objects.requireNonNull(at, "a container at a position is at one");
            }
        }

        /** One that stands at none, which an operation answered: told from another by what it is
         *  made of. */
        record Made(Core expression) implements ContainerOf {

            public Made {
                Objects.requireNonNull(expression, "a container made is made of something");
            }
        }

        /** One a dependency answered, told from another by the evaluation that answered it and
         *  the places inside the answer it stands at. */
        record InAnAnswer(AnEvaluation evaluation, List<TermPath.Step> at)
                implements ContainerOf {

            public InAnAnswer {
                Objects.requireNonNull(evaluation, "an answer is the answer of some evaluation");
                at = List.copyOf(at);
            }
        }
    }

    /**
     * Each element of a container that {@code e} reads a name for: the elements, and not the
     * names for a position that is no container's element or for a value an operation made.
     *
     * <p>What tells two names for two elements of one container from one name met twice, and a
     * name for an entry's key from one for its value. A position inside a container says an element
     * and not which one, so that is the position's to say and not this's.
     */
    List<ElementStood> elementsStoodForIn(Core e, DeclarationNewtypes newtypes) {
        Set<BindingId> made = new HashSet<>();
        Set<BindingId> read = new LinkedHashSet<>();
        walkNames(e, made, read);
        // A name bound inside the expression is a different value on each application of what
        // binds it, as a closure's parameter is on each element it is handed, and so no one
        // element the comparison is read of.
        read.removeAll(made);
        List<ElementStood> out = new ArrayList<>();
        for (BindingId each : read) {
            ElementStood stood = elementStoodBy(each, newtypes, 0);
            if (stood != null) {
                out.add(stood);
            }
        }
        return List.copyOf(out);
    }

    /** The element {@code name} is a name for, through the names it was only given. */
    private ElementStood elementStoodBy(BindingId name, DeclarationNewtypes newtypes, int depth) {
        // The entry a lookup picked out of a map filed from an answer's list is an element of that
        // list, as the entry of a map filed from the input's is.
        AnAnswerAt entry = names.placeInAnAnswer(name);
        if (entry != null && !entry.steps().isEmpty()
                && entry.steps().getLast() instanceof TermPath.Step.Element) {
            return new ElementStood(name, new ContainerOf.InAnAnswer(entry.evaluation(),
                    entry.steps().subList(0, entry.steps().size() - 1)), HeldIn.Part.ELEMENT);
        }
        return switch (names.roleOf(name)) {
            case BindingRole.Element(HeldIn held) -> new ElementStood(name,
                    pathOf(held.container(), newtypes) instanceof PathResolution.At(TermPath at)
                            ? new ContainerOf.AtAPosition(at)
                            : new ContainerOf.Made(Core.withoutStanding(held.container())),
                    held.part());
            // A name given the position of an element, as the value of an entry a lookup
            // answered is.
            case BindingRole.Root(TermPath path) -> stoodAt(name, path);
            // A name only given another is that one, so that the same element met under two names
            // is not two. Bounded by how far names are given names, which is a few.
            case BindingRole.Alias(Core given) -> depth < KEPT_NAMES_APART
                    && Core.withoutStanding(given) instanceof Core.Read root
                    ? elementStoodBy(root.binding(), newtypes, depth + 1) : null;
            case BindingRole.ElementOfSeveral _, BindingRole.Unknown _ -> null;
        };
    }

    /** How many names given names are followed to the element. */
    private static final int KEPT_NAMES_APART = 16;

    private static ElementStood stoodAt(BindingId name, TermPath path) {
        if (path.steps().isEmpty()) {
            return null;
        }
        TermPath held = new TermPath(path.head(), path.steps().subList(0, path.steps().size() - 1));
        ContainerOf in = new ContainerOf.AtAPosition(held);
        return switch (path.steps().getLast()) {
            case TermPath.Step.Element _ -> new ElementStood(name, in, HeldIn.Part.ELEMENT);
            case TermPath.Step.Key _ -> new ElementStood(name, in, HeldIn.Part.KEY);
            case TermPath.Step.Field _, TermPath.Step.Refine _ -> null;
        };
    }

    /**
     * The entries the names in force are the value of, by the name: what is stated of such a name
     * is stated of the entry the lookup answered, and of no other element of the container.
     */
    public Map<BindingId, EntryLookedUp> entriesLookedUp() {
        return names.selected();
    }

    /**
     * The position the key {@code key} makes of the element at {@code element} stands at, or null
     * where it is no position: a closure answering a field of its parameter, which is what each
     * entry of a map filed from a list is under.
     */
    public TermPath keyOfTheElement(Core.Block key, TermPath element,
                                    DeclarationNewtypes newtypes) {
        InputReads handed = new InputReads(names.naming(key.params().getFirst().binding(),
                element), alternatives, declared, dependencies, applied);
        return handed.forkedOn(key.body(), newtypes) instanceof PathResolution.At(TermPath at)
                ? at : null;
    }

    /**
     * The same, where what the arm binds is one of the values the scrutinee's set holds — or the
     * one value it stands for, where that value is written out. A closure handed one of the
     * values a list was written with matches that value, and the name under the arm is the value
     * as the arm takes it, as it would be one member of the set.
     *
     * <p>Only where the arm's carriers are the values themselves. A case that binds what an optional
     * holds binds something under the value that was matched rather than the value, so the members
     * of the set are not what the name stands for — and a set narrowed as though they were would
     * name every member one step too high.
     *
     * <p>Nothing is narrowed where a member cannot be told which case it is. What makes the set an
     * answer is that it holds every value the name can take, and a filter that let through what it
     * could not classify would be keeping a member the arm excludes, while one that dropped it would
     * be losing a member the arm admits. Neither is the set, so the name is left with none.
     *
     * <p>Which a member is is {@link WrittenCase}'s answer, held to the atoms the arm's cases cover
     * ({@link Core.ResolvedPattern#takes}), so a member under a case that is itself a sum is kept by
     * the arm written for the sum, and a number is the primitive it is.
     *
     * <p>And nothing is narrowed to no members. An arm admitting none of what the container holds is
     * an arm no value reaches, so the name inside it stands for nothing — which is what a name with
     * no meaning here already says, and is not a set of no members.
     */
    private InputReads admitting(Core scrutinee, Core.Case arm, Symbols symbols,
                                 DeclarationNewtypes newtypes) {
        ReadMeaning.OneOf one = pluralityOf(scrutinee, symbols, newtypes);
        List<ReadMeaning.Occurrence> values;
        if (one != null) {
            values = one.asWritten();
        } else {
            Denotation stands = standing(new Denotation(scrutinee, this), symbols, newtypes,
                    new HashSet<>());
            if (WrittenCase.of(stands.value()).isEmpty()) {
                return denotingWhatWasMatched(scrutinee, arm, symbols, newtypes);
            }
            values = List.of(ReadMeaning.Occurrence.always(stands));
        }
        for (CaseSelector selector : arm.pattern().selectors()) {
            if (!(selector.refinement() instanceof souther.compiler.types.Refinement.Direct)) {
                return this;
            }
        }
        // What each occurrence was kept by stays with it: the arm takes some of them out, and
        // whether a container holds the ones left is what it was before.
        List<ReadMeaning.Occurrence> left = new ArrayList<>();
        for (ReadMeaning.Occurrence each : values) {
            Optional<TypeSymbol> written = WrittenCase.of(each.value().value());
            if (written.isEmpty()) {
                return this;
            }
            if (arm.pattern().takes(written.get())) {
                left.add(each);
            }
        }
        if (left.isEmpty()) {
            return this;
        }
        Map<BindingId, List<ReadMeaning.Occurrence>> wider = new LinkedHashMap<>(alternatives);
        wider.put(arm.binder().binding(), left);
        return new InputReads(names, wider, declared, dependencies, applied);
    }

    /**
     * The same, where the scrutinee is what a call answered: the name stands for the value that was
     * matched, which is that answer.
     *
     * <p>Which value a name is and what is known of the case it was taken as are two facts. Nothing
     * here narrows what a call answered — there is no position to narrow and no set to filter — but
     * {@code Amount as current} over {@code read(1)} is still the value {@code read(1)} answered, and
     * a reader asking what {@code current} is goes on to the call. Given no meaning, the name was a
     * value nothing could say anything about, and a comparison over it was one this compiler named a
     * column for when it was written as the call and read nothing of when it was written through the
     * name.
     *
     * <p><b>Only an answer, because only there is the narrowing nothing to lose.</b> What a call
     * answers is a value this reading holds nothing inside of, so the name read through to it is read
     * as the call — what the arm took it as adds nothing a reader could have looked at. A value the
     * body
     * built is one this reading looks inside, and read through without the arm it is every case it
     * could be: {@code B as b} over {@code if flag then A {..} else B {..}} would be the choice on
     * {@code flag}, and over a written {@code A} a construction asked for a field it has none of.
     * Which is why the scrutinee is followed through its names first ({@link #standing}): what
     * decides is the value they stand for and not how the {@code match} spelled it.
     *
     * <p>Only the name of the matched value ({@link Core.ArmBinding.Selected}). What stands under
     * an optional's present carrier is not the value that was matched, and a name for it read as
     * the scrutinee would stand for the optional it was opened from.
     *
     * <p>And only where the scrutinee is at no position. One that stands at a position the arm does
     * not narrow, or at one of several, names a place, and a name read through to it would stand at
     * the place as it is — wider than the case the arm took.
     */
    private InputReads denotingWhatWasMatched(Core scrutinee, Core.Case arm, Symbols symbols,
                                              DeclarationNewtypes newtypes) {
        if (!(arm.binding() instanceof Core.ArmBinding.Selected selected)
                || !(forkedOn(scrutinee, newtypes) instanceof PathResolution.NotAPosition)
                || !answered(standing(new Denotation(scrutinee, this), symbols, newtypes,
                        new HashSet<>()).value())) {
            return this;
        }
        return and(selected.binder(), scrutinee);
    }

    /**
     * Whether {@code e} is what a call answered: one the body reaches outside itself, or an
     * operation of the language the tree keeps standing. Either way a value nothing in this tree
     * builds.
     */
    private static boolean answered(Core e) {
        return switch (Core.withoutStanding(e)) {
            case Core.Call _, Core.PreservedCall _ -> true;
            case null, default -> false;
        };
    }

    /**
     * The values {@code e} can stand for, or null where they are not written out.
     *
     * <p>Through the names that stand for one value, which is what a scrutinee usually is: a body
     * naming what it matches, and a helper expanded into one binding the call's argument to its own
     * parameter, leave a run of names between the {@code match} and the element. Read one step, an
     * arm inside such a helper would narrow nothing and the reading would stop at the first name.
     *
     * <p>Following is this reader's own and is not written into {@link #meaningOf}. That answers
     * what a name is, one step, for every reader; whether a reader may go on through a name that
     * stands for one value is what the answer licenses rather than something it does.
     *
     * <p>The same walk a container is found by ({@link #standing}), asked for what is standing at
     * the end of it rather than for a list written there. Two walks over the run of names between a
     * {@code match} and what it matches would be two answers about which names may be gone through,
     * and the day they differed the arm would narrow a set the arithmetic never met.
     */
    private ReadMeaning.OneOf pluralityOf(Core e, Symbols symbols,
                                          DeclarationNewtypes newtypes) {
        Denotation standing = standing(new Denotation(e, this), symbols, newtypes,
                new HashSet<>());
        return Core.withoutStanding(standing.value()) instanceof Core.Read name
                && standing.at().meaningOf(name, symbols, newtypes) instanceof ReadMeaning.OneOf one
                ? one : null;
    }

    /**
     * Whether every row takes {@code arm} of a {@code match} on {@code scrutinee} — true where every
     * case the scrutinee can be is one the arm takes, false where none is, and empty where which
     * arm is taken turns on the row.
     *
     * <p>Known only where every value the scrutinee can stand for settles its own case
     * ({@link WrittenCase}) — a construction, an optional's carrier, a value of a primitive type.
     * A helper handed such a value at the call matches what it was handed, and which of its arms
     * that takes is settled before any row is written: there is no position under the
     * {@code match} for a row to put a case at, and none is needed.
     *
     * <p>One answer for every reader of an arm, the ways a body is walked and what reaching the arm
     * states alike, so an arm no row takes is neither walked nor a narrowing nobody can read.
     */
    public Optional<Boolean> whetherEveryRowTakes(Core.Case arm, Core scrutinee, Symbols symbols,
                                                  DeclarationNewtypes newtypes) {
        return whetherEveryRowTakes(arm, casesWritten(scrutinee, symbols, newtypes));
    }

    /**
     * The same, of the cases the scrutinee was already read to be ({@link #casesWritten}) — which
     * is one question per {@code match} however many arms are asked about it.
     */
    public static Optional<Boolean> whetherEveryRowTakes(Core.Case arm, Set<TypeSymbol> written) {
        if (written == null) {
            return Optional.empty();
        }
        long taken = written.stream().filter(arm.pattern()::takes).count();
        if (taken == written.size()) {
            return Optional.of(true);
        }
        return taken == 0 ? Optional.of(false) : Optional.empty();
    }

    /**
     * The cases {@code e} can be here, where every value it can stand for settles its own case
     * ({@link WrittenCase}) — or null where any of them does not.
     *
     * <p>The value a name stands for, followed as far as it goes ({@link #standing}), and where that
     * is a name standing for one of several written values ({@link ReadMeaning.OneOf}), each of
     * them.
     */
    public Set<TypeSymbol> casesWritten(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        Denotation stands = standing(new Denotation(e, this), symbols, newtypes, new HashSet<>());
        Optional<TypeSymbol> one = WrittenCase.of(stands.value());
        if (one.isPresent()) {
            return Set.of(one.get());
        }
        if (!(Core.withoutStanding(stands.value()) instanceof Core.Read name
                && stands.at().meaningOf(name, symbols, newtypes) instanceof ReadMeaning.OneOf many)) {
            return null;
        }
        // Of every value it may be, kept or not: a case none of them is, is a case no kept one is.
        Set<TypeSymbol> out = new LinkedHashSet<>();
        for (Denotation each : many.everyValueItMayBe()) {
            Optional<TypeSymbol> written =
                    WrittenCase.of(standing(each, symbols, newtypes, new HashSet<>()).value());
            if (written.isEmpty()) {
                return null;
            }
            out.add(written.get());
        }
        return out;
    }

    /**
     * The reading an arm's answer is read in: this, with what choosing that arm binds entered.
     *
     * <p>Asked of {@link Choice.Decides} rather than of the node an arm stands in, so that a way of
     * deciding added to the language stops here until somebody says what choosing it binds. Written
     * in this vocabulary and not shared with the one next door: what a name means to a reading of
     * the inputs is this class's answer throughout, and {@link souther.compiler.check.Terms} gives
     * the same sum the answer its own readers speak.
     */
    public InputReads choosing(Choice.Decides decidedBy, Symbols symbols,
                               DeclarationNewtypes newtypes) {
        return switch (decidedBy) {
            // A condition binds nothing. Which way it went is settled where the arm is read.
            case Choice.Decides.ACondition _ -> this;
            case Choice.Decides.ACase(Core.Case arm, Core scrutinee) ->
                    insideArmOn(scrutinee, arm, symbols, newtypes);
            // The invariant held, so the name the attempt writes stands for what was built.
            case Choice.Decides.ItWasBuilt(Core.IfConstructed attempt) ->
                    and(attempt.binder(), attempt.construct());
            // A departure is taken where nothing was built, so it has nothing to enter.
            case Choice.Decides.ItDeparted _ -> this;
            // An operation defined by cases answers a value the call was already given. It
            // introduces no name.
            case Choice.Decides.ByArgumentRelations _ -> this;
        };
    }

    /**
     * This reading inside the arm {@code decidedBy} took, for a walk that stands in the names
     * {@code at} and not in the ones here.
     *
     * <p>A query for where a value came from crosses bindings on the way to a choice, and reads the
     * choice's arms in those. An arm that binds a name opens it on top of them ({@link #choosing}),
     * which is the one place that says what such a name stands for. The whole reading is handed
     * back and not the names of it: what the arm adds is not all in the names, and a walk that took
     * only them would lose the rest the first time a reader of it asked.
     *
     * <p>The reading at {@code at} itself where the declarations of this input carry no symbols to
     * read an arm under.
     */
    InputReads insideArm(BindingEnvironment at, Choice.Decides decidedBy,
                         DeclarationNewtypes newtypes) {
        InputReads there = withNames(at);
        Symbols symbols = declared.symbols();
        return symbols == null ? there : there.choosing(decidedBy, symbols, newtypes);
    }

    /** Whether a name was given a value on the way to this reading ({@link #handedOver}). */
    boolean hasGiven() {
        return !applied.given().isEmpty();
    }

    /** This reading, standing in the names {@code at}. */
    InputReads withNames(BindingEnvironment at) {
        return at == names ? this
                : new InputReads(at, alternatives, declared, dependencies, applied);
    }

    /**
     * The reading a child is read in, {@code step} being the way from its parent into it
     * ({@link ScopeStep#forEachChild}).
     *
     * <p>A block's body is read in the reading the block stands in. Its parameters are given where
     * something calls it, which is no position of this behavior's input, and a name nothing entered
     * stands for no position already.
     */
    public InputReads entering(ScopeStep step, Symbols symbols, DeclarationNewtypes newtypes) {
        return switch (step) {
            case ScopeStep.Same _ -> this;
            case ScopeStep.Let(Core.LetIn binding) -> and(binding.binder(), binding.value());
            case ScopeStep.Chosen(Choice.Decides decidedBy) ->
                    choosing(decidedBy, symbols, newtypes);
            case ScopeStep.Block(Core.Block block) -> handedWhatOptionsHold(block, symbols,
                    newtypes);
        };
    }

    /**
     * The same, inside {@code block}, with each parameter an operation hands what an option holds
     * standing for that value ({@link #whatItHolds}, {@link #holding}).
     *
     * <p>An option holds one value or none, and an operation applying its closure to every element
     * of one hands the parameter that value, so a statement inside the closure is about it — the
     * same value the name under an arm opening the option stands for, and read the same way.
     */
    private InputReads handedWhatOptionsHold(Core.Block block, Symbols symbols,
                                             DeclarationNewtypes newtypes) {
        InputReads out = this;
        for (Core.Binder param : block.params()) {
            if (param != null && param.binding() != null
                    && names.roleOf(param.binding()) instanceof BindingRole.Element(var held)
                    && held.ofAnOption()) {
                out = out.holding(param.binding(),
                        out.whatItHolds(held.container(), symbols, newtypes), newtypes)
                        .turningOn(param.binding(),
                                List.of(new Denotation(held.container(), out)));
            }
        }
        return out;
    }

    /** The same, inside what {@code binder} binds. */
    public InputReads and(Core.Binder binder, Core value) {
        BindingEnvironment inside = names.inside(binder, value);
        return inside == names ? this
                : new InputReads(inside, alternatives, declared, dependencies, applied);
    }

    /**
     * Where {@code e} stands, read here ({@link PathResolution}): a position, and never a narrowing
     * of one to several cases ({@link PathResolution#heldAt}).
     *
     * <p>Answered once for each node asked here. Every reader of a condition asks where its parts
     * stand — the arithmetic of a side, whether a value is the same on every run, whether two
     * cases are written out — and each asks it of the same nodes in the same reading. What it
     * comes to turns on nothing but the node and this reading, which does not change; the node
     * and not one equal to it, since what this reading takes a node as is taken of that node
     * ({@link #taken}).
     */
    public PathResolution pathOf(Core e, DeclarationNewtypes newtypes) {
        if (paths == null) {
            paths = new IdentityHashMap<>();
            pathsUnder = newtypes;
        } else if (pathsUnder != newtypes) {
            return InputPath.of(e, names, newtypes, this).heldAt();
        }
        PathResolution held = paths.get(e);
        if (held == null) {
            held = InputPath.of(e, names, newtypes, this).heldAt();
            paths.put(e, held);
        }
        return held;
    }

    /** What a name means here, for a walk that goes on in this reading ({@link InputPath}). */
    BindingEnvironment names() {
        return names;
    }

    /**
     * What a fork on {@code e} reads: where it stands, with what the arms above already left it.
     *
     * <p>Beside {@link #pathOf} because the two questions part at a name an arm bound over several
     * cases. The value stands at the sum's position; a fork on it is asked of the cases the arm
     * left, so that an arm inside naming one of them narrows the same narrowing further rather than
     * the position afresh ({@link DeclaredInput#taking}).
     */
    public PathResolution forkedOn(Core e, DeclarationNewtypes newtypes) {
        return InputPath.of(e, names, newtypes, this);
    }

    /** Where in the element handed to {@code binding} the value a walk answered stands, or null
     *  where the walk answered no place of it ({@link ElementProjection}). */
    ElementProjection projectionAt(BindingId binding) {
        return names.projectionAt(binding);
    }

    /**
     * What {@code answer}, made of the element handed to {@code element}, is as far as which
     * answers are equal goes, through the names the body bound on the way — or null where it is no
     * place of that element and no newtype wearing one ({@link OnePerElement.Answered}).
     */
    public OnePerElement.Answered answeredOf(Core answer, BindingId element,
                                             DeclarationNewtypes newtypes) {
        return element == null ? null
                : OnePerElement.Answered.of(answer, element, heldByTheBody(), newtypes);
    }

    /**
     * Which occurrences of the input the list {@code list} holds one value each of, and where what
     * each of {@code reads} takes out of each element of it stands among the places of the input
     * — or null where the list is not shown to hold one value for each of some occurrences.
     *
     * <p>One walk for both of the runs a list can be. A list holding one value for each element of
     * one container ({@link ElementQuestion#ONE_PER_ELEMENT}) is the occurrences of a place inside
     * that one occurrence of the container. A list put end to end out of what a closure answered of
     * each element holds a value for each occurrence of a place inside many containers, and how
     * often a value occurs in it is how often it occurs among all of them. The steps down are the
     * ones the first question crosses ({@link InputPath#oneStepBeneath}); a map, which answers one
     * value for each element whatever it built; and the flattening: what a closure answers is read
     * down the same steps to a list at a place of the element it was handed, and that element is
     * one of every occurrence of the place the list flattened holds.
     *
     * <p>Which run the list is turns on the operations it was made by and on nothing read off its
     * elements, so every read is carried down the one walk and each comes to where it comes to in
     * the same run: a key and a value read off one element stand in the same element of the same
     * container. A map that built something of each element is crossed by taking it apart where a
     * read takes something out of it; a read the construction answers nothing for comes to no
     * place, and the walk goes on for the others.
     *
     * <p>A list some of whose elements an operation kept by a statement is crossed too, when
     * {@code keeping} says so, and the call is handed back among the answer's {@code keptBy}: a
     * count then counts only the occurrences the statement keeps. The call is handed back where it
     * stands, and what it keeps by is read down the same list to the same container, whatever a
     * map beneath it made of an element on the way. Across the lists of a flattening it is about
     * the elements of those lists, so a flattening is crossed beneath one only where nothing
     * between them made anything new of an element.
     *
     * <p>Every step is asked of the list as handed to it and as it came to be reached, since which
     * values are equal is what both runs are read for, and what a wider type calls equal is not
     * shown to be what the narrower one does ({@link InputPath#goesOnThrough}).
     *
     * @param reads   what is taken out of each element of the list, each answered in its place in
     *                {@link Occurrences#reads()}
     * @param keeping the list a call keeps some of the elements of by a statement, or null where
     *                the call is no such operation
     */
    public Occurrences occurrencesOf(Core list, List<ReadOff> reads,
                                     Function<Core, Core> keeping, Symbols symbols,
                                     DeclarationNewtypes newtypes) {
        Core asked = list;
        Denotation standing = standing(list, symbols, newtypes);
        // What each read takes out of an element of the list reached, or null where it was taken
        // apart against a construction that answered nothing for it.
        List<ReadOff> sought = new ArrayList<>(reads);
        List<Denotation> keptBy = new ArrayList<>();
        // Whether anything new was made of an element beneath the first operation that kept some.
        boolean madeNewBeneath = false;
        // A step to a name is a step over the binding graph, and a name come round to again is one
        // already answered for; a step down an operation stays inside one finite tree.
        Set<BindingId> met = new HashSet<>();
        while (true) {
            if (!InputPath.goesOnThrough(asked, standing.value(),
                    ElementQuestion.ONE_PER_ELEMENT)) {
                return null;
            }
            InputReads where = standing.at();
            if (where.pathOf(standing.value(), newtypes) instanceof PathResolution.At(
                    TermPath container)) {
                return new Occurrences.OfOneContainer(container,
                        placedIn(sought, container.element()), keptBy);
            }
            if (Core.withoutStanding(standing.value()) instanceof Core.Read name
                    && !met.add(name.binding())) {
                return null;
            }
            Core beneathKept = keeping == null ? null : keeping.apply(standing.value());
            if (beneathKept != null) {
                keptBy.add(standing);
                asked = beneathKept;
                standing = where.standing(asked, symbols, newtypes);
                continue;
            }
            MapStep mapped = throughAMap(standing, sought, symbols, newtypes);
            if (mapped != null) {
                madeNewBeneath |= !keptBy.isEmpty() && mapped.madeNew(newtypes);
                sought = mapped.reads();
                asked = mapped.from();
                standing = where.standing(asked, symbols, newtypes);
                continue;
            }
            // A flattening of one value or none for each element is a map of the elements it
            // answers one for, and keeps those as any operation keeping some keeps them: by what
            // its size counts.
            OneOrNone ofOne = throughAFlatteningOfOneOrNone(standing, sought, symbols, newtypes);
            if (ofOne != null && (!ofOne.someAnswerNone() || keeping != null)) {
                madeNewBeneath |= !keptBy.isEmpty() && ofOne.madeNew();
                if (ofOne.someAnswerNone()) {
                    keptBy.add(standing);
                }
                sought = ofOne.reads();
                asked = ofOne.from();
                standing = where.standing(asked, symbols, newtypes);
                continue;
            }
            InputPath.Beneath step = InputPath.oneStepBeneath(standing.value(),
                    ElementQuestion.ONE_PER_ELEMENT, where.names(), newtypes,
                    closure -> blockOf(where, closure, symbols, newtypes));
            if (step != null) {
                sought = after(sought, step.answered());
                madeNewBeneath |= !keptBy.isEmpty() && !step.answered().at().fields().isEmpty();
                asked = step.from();
                standing = where.standing(asked, symbols, newtypes);
                continue;
            }
            // What a statement kept some by is about the elements of the lists the flattening put
            // end to end, so each is one of theirs and no value made of one.
            boolean kept = !keptBy.isEmpty();
            Flattened flattened = kept && madeNewBeneath ? null
                    : flattenedKeysAt(standing, sought, kept, keeping, keptBy, symbols, newtypes);
            return flattened == null ? null
                    : new Occurrences.AcrossContainers(flattened.outer(), flattened.reads(),
                            keptBy);
        }
    }

    /**
     * What each element of a list a walk hands a closure is, as a value made of an element of a
     * container of the input: the closure's name for it, held to what the operations beneath made
     * of that element.
     *
     * <p>The value a map answered of an element is its closure's body with its parameter standing
     * for the element, and a flattening of one value or none answers the one value its arm wrote:
     * each is held under the name the walk above hands it by, so a reading of the element read
     * through the names reads what it was made of, down to the element of the input it was made
     * from. What is read of it is read of that element and no other.
     *
     * <p>Where arms answering a value are chosen by the case of one place of the element, the
     * element is made by the arm its case is taken by, and each arm is held with the cases it
     * takes: whatever is read of the element is read of each arm and chosen by that one case, so
     * two things read of one element are read of the one arm that made it.
     *
     * @param elements where the elements it was made of stand, narrowed to the case the arm
     *                 answering it took where one arm answers
     * @param element  the name the element of the input arrives on
     * @param subject  the place of the element whose case chooses the arm, or null where one arm
     *                 makes every element
     * @param arms     the ways an element is made, one where {@code subject} is null
     * @param keptBy   the calls that kept some of the elements, outermost first, each where it
     *                 stands
     */
    public record WalkedElement(TermPath elements, BindingId element, ElementProjection subject,
                                List<Arm> arms, List<Denotation> keptBy) {

        /**
         * One way an element is made.
         *
         * @param cases    the cases of the subject this arm takes, or null where it is the one way
         * @param held     what each name on the way holds, the walks' names among them
         * @param standing where in the element each name an arm on the way bound stands
         */
        public record Arm(CasesLeft cases, Map<BindingId, Core> held,
                          Map<BindingId, ElementProjection> standing) {

            public Arm {
                held = Map.copyOf(held);
                standing = Map.copyOf(standing);
            }
        }

        public WalkedElement {
            Objects.requireNonNull(elements, "the elements stand somewhere");
            Objects.requireNonNull(element, "an element arrives on some name");
            arms = List.copyOf(arms);
            keptBy = List.copyOf(keptBy);
            boolean oneWay = arms.size() == 1 && arms.getFirst().cases() == null;
            if (subject == null ? !oneWay
                    : arms.size() < 2 || arms.stream().anyMatch(arm -> arm.cases() == null)) {
                throw new IllegalArgumentException("an element is made one way, or by the arm"
                        + " each case of a place is taken by");
            }
            for (int i = 0; subject != null && i < arms.size(); i++) {
                for (int j = i + 1; j < arms.size(); j++) {
                    if (arms.get(i).cases().meet(arms.get(j).cases()) != null) {
                        throw new IllegalArgumentException("two arms making an element take one"
                                + " case of " + subject);
                    }
                }
            }
        }
    }

    /**
     * What each element of {@code list} handed to {@code walked} is made of ({@link
     * WalkedElement}) — or null where the list is not the elements of a container of the input,
     * each made into one value by maps and flattenings of one value or none, some of them kept by
     * an operation {@code keeping} names.
     *
     * <p>A name an arm bound is read only at the walk the arm is in, the last one down: one bound
     * further up is a place of a value made of the element, which no place of the element is.
     *
     * <p>Several arms answering a value, of a flattening or of a map's closure over the elements
     * of a container, are read where each is chosen by one case of one place of the element and
     * by nothing else on its way ({@link AnArmAnswered#taken}): the case then says
     * which arm made an element, and no two arms make one. An arm chosen otherwise, or two
     * choices on the way, leave which arm made an element to something no case says.
     */
    public WalkedElement walkedElementOf(Core list, BindingId walked,
                                         Function<Core, Core> keeping, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        Denotation standing = standing(list, symbols, newtypes);
        BindingId current = walked;
        Map<BindingId, Core> held = new LinkedHashMap<>(heldByTheBody());
        Map<BindingId, ElementProjection> bound = Map.of();
        ElementProjection subject = null;
        List<WalkedElement.Arm> arms = null;
        List<Denotation> keptBy = new ArrayList<>();
        Set<BindingId> met = new HashSet<>();
        while (true) {
            InputReads where = standing.at();
            if (where.pathOf(standing.value(), newtypes) instanceof PathResolution.At(
                    TermPath container)) {
                return arms != null
                        ? new WalkedElement(container.element(), current, subject, arms, keptBy)
                        : narrowedToTheArm(container.element(), current, held, bound, keptBy);
            }
            if (Core.withoutStanding(standing.value()) instanceof Core.Read name
                    && !met.add(name.binding())) {
                return null;
            }
            Core beneathKept = keeping == null ? null : keeping.apply(standing.value());
            if (beneathKept != null) {
                keptBy.add(standing);
                standing = where.standing(beneathKept, symbols, newtypes);
                continue;
            }
            // What an arm bound is a place of the element the arm was handed, and a walk beneath
            // makes that element of another.
            if (!bound.isEmpty() || arms != null) {
                return null;
            }
            MapStep mapped = throughAMap(standing, List.of(), symbols, newtypes);
            // A map of a container's elements whose closure answers by the case of a place of
            // the element is made by the arm that case takes, as a flattening answering one value
            // on each arm is.
            List<AnArmAnswered> answered = new ArrayList<>();
            boolean madeByArms = mapped != null
                    && where.everyElementOf(mapped.from(), newtypes)
                            instanceof PathResolution.At(TermPath outer)
                    && armsAnswering(mapped.closure().body(), where, new LinkedHashMap<>(held),
                            Map.of(), ChoicesOnTheWay.NONE, outer, ArmsEndIn.A_VALUE, answered,
                            symbols, newtypes)
                    && answered.size() > 1;
            if (mapped != null && !madeByArms) {
                held.put(current, mapped.closure().body());
                current = mapped.closure().params().getFirst().binding();
                standing = where.standing(mapped.from(), symbols, newtypes);
                continue;
            }
            AFlattening flattening = madeByArms ? null : aFlattening(standing, symbols, newtypes);
            if (!madeByArms && (flattening == null
                    || !armsAnswering(flattening.closure().body(), where,
                            new LinkedHashMap<>(held), Map.of(), ChoicesOnTheWay.NONE,
                            flattening.outer(), ArmsEndIn.A_LIST_OF_ONE_OR_NONE, answered,
                            symbols, newtypes))) {
                return null;
            }
            List<AnArmAnswered> values = answered.stream()
                    .filter(each -> each.value() != null).toList();
            if (values.isEmpty()) {
                return null;
            }
            if (values.size() < answered.size()) {
                keptBy.add(standing);
            }
            if (values.size() == 1) {
                held.putAll(values.getFirst().held());
                held.put(current, values.getFirst().value());
                bound = values.getFirst().standing();
            } else {
                subject = values.getFirst().taken() == null ? null
                        : values.getFirst().taken().narrowedFrom();
                arms = new ArrayList<>();
                for (AnArmAnswered each : values) {
                    if (subject == null || each.taken() == null
                            || !subject.equals(each.taken().narrowedFrom())) {
                        return null;
                    }
                    Map<BindingId, Core> made = new LinkedHashMap<>(held);
                    made.putAll(each.held());
                    made.put(current, each.value());
                    arms.add(new WalkedElement.Arm(each.taken().narrowing(), made,
                            each.standing()));
                }
            }
            current = madeByArms ? mapped.closure().params().getFirst().binding()
                    : flattening.element();
            standing = where.standing(madeByArms ? mapped.from() : flattening.from(),
                    symbols, newtypes);
        }
    }

    /** An element the walk {@code element} is handed by holds as it stands at {@code elements},
     *  some of them kept by {@code keptBy}: nothing beneath made anything of it. */
    public WalkedElement walkedAsItStands(TermPath elements, BindingId element,
                                          List<Denotation> keptBy) {
        return new WalkedElement(elements, element, null,
                List.of(new WalkedElement.Arm(null, heldByTheBody(), Map.of())), keptBy);
    }

    /**
     * The walked element of {@code elements}, with the case every name the arm bound narrows the
     * element to taken into where the elements stand: what an arm answering one value of an
     * element is read of is that element as the case the arm took, which is a place of its own.
     */
    private static WalkedElement narrowedToTheArm(TermPath elements, BindingId element,
                                                  Map<BindingId, Core> held,
                                                  Map<BindingId, ElementProjection> bound,
                                                  List<Denotation> keptBy) {
        List<TermPath.Step> narrowing = null;
        for (ElementProjection each : bound.values()) {
            List<TermPath.Step> leading = new ArrayList<>();
            for (TermPath.Step step : each.steps()) {
                if (!(step instanceof TermPath.Step.Refine)) {
                    break;
                }
                leading.add(step);
            }
            if (narrowing == null || leading.size() < narrowing.size()) {
                narrowing = leading;
            }
        }
        if (narrowing == null || narrowing.isEmpty()) {
            return new WalkedElement(elements, element, null,
                    List.of(new WalkedElement.Arm(null, held, bound)), keptBy);
        }
        Map<BindingId, ElementProjection> within = new LinkedHashMap<>();
        for (Map.Entry<BindingId, ElementProjection> each : bound.entrySet()) {
            List<TermPath.Step> steps = each.getValue().steps();
            if (!steps.subList(0, narrowing.size()).equals(narrowing)) {
                return null;
            }
            within.put(each.getKey(),
                    new ElementProjection(steps.subList(narrowing.size(), steps.size())));
        }
        return new WalkedElement(new ElementProjection(narrowing).from(elements), element, null,
                List.of(new WalkedElement.Arm(null, held, within)), keptBy);
    }

    /**
     * What {@code answer}, made of the element of {@code walked} it reads, takes out of it, as
     * far as which values are equal goes, read of each arm making the element and chosen by the
     * case that chooses the arm — or null where on some arm it is no way through what that
     * element is ({@link ElementProjection#readAsAKey}).
     *
     * <p>The answer may make the choice itself: where the element is made one way, an answer
     * whose arms are chosen by the case of one place of the element, each answering a key, is
     * read as a key chosen by that case ({@link ElementKey.ByCase}), as one made by the walks
     * beneath is. Two choices, one beneath and one in the answer, leave which way an element is
     * read to something no one case says.
     */
    public ElementKey keyOf(Core answer, WalkedElement walked, Symbols symbols,
                            DeclarationNewtypes newtypes) {
        List<ElementKey.ByCase.Arm> arms = new ArrayList<>();
        ElementProjection subject = walked.subject();
        for (WalkedElement.Arm arm : walked.arms()) {
            List<AnArmAnswered> chosen = new ArrayList<>();
            if (!armsAnswering(answer, this, new LinkedHashMap<>(arm.held()), arm.standing(),
                    ChoicesOnTheWay.NONE, walked.elements(), ArmsEndIn.A_VALUE, chosen, symbols,
                    newtypes)) {
                return null;
            }
            if (chosen.size() > 1 && subject == null) {
                subject = chosen.getFirst().taken() == null ? null
                        : chosen.getFirst().taken().narrowedFrom();
                if (subject == null) {
                    return null;
                }
            } else if (chosen.size() > 1) {
                return null;
            }
            for (AnArmAnswered each : chosen) {
                ReadOff read = ElementProjection.readAsAKey(each.value(), ReadOff.ITSELF,
                        walked.element(), each.standing(), each.held(), newtypes);
                if (read == null || read.placed() == null) {
                    return null;
                }
                if (subject == null) {
                    return new ElementKey.At(read.placed().at());
                }
                CasesLeft cases = chosen.size() == 1 ? arm.cases()
                        : each.taken() == null || !subject.equals(each.taken().narrowedFrom())
                                ? null : each.taken().narrowing();
                if (cases == null) {
                    return null;
                }
                arms.add(new ElementKey.ByCase.Arm(cases, read.placed().at()));
            }
        }
        return ElementKey.byCase(subject, arms);
    }

    /**
     * Where the elements of {@code walked} put their number in place of the ones before, where
     * {@code answer}, made of the element, says so on arms chosen by the case of one place of it,
     * each answering {@code true} or {@code false}: that place, the cases of the arms answering
     * {@code true}, and the direction the walk was handed the elements in — or null where the
     * element is made otherwise than one way, the arms are chosen otherwise, an arm answers
     * anything else, or nothing shows the order.
     *
     * <p>The order is what the list walked holds them in, read through the operations declared to
     * turn a list round and no other ({@link #inTheOrderOf}), turned round once more where the
     * walk hands the last of them first: what is shown is of the elements the list holds, and
     * they are the elements {@code walked} stand at or no order is shown of them.
     *
     * @param list            the list the walk was handed
     * @param inTheListsOrder whether the walk hands the elements in the order {@code list}
     *                        holds them, rather than from the last of them
     */
    public NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut putsOf(
            Core answer, WalkedElement walked, Core list, boolean inTheListsOrder,
            Symbols symbols, DeclarationNewtypes newtypes) {
        RunSource.TraversalOrder order = null;
        for (TraversalDirection direction : TraversalDirection.values()) {
            if (inTheOrderOf(list, direction, newtypes) instanceof PathResolution.At(
                    TermPath elements) && elements.equals(walked.elements())) {
                order = new RunSource.TraversalOrder(elements,
                        inTheListsOrder ? direction : direction.reversed());
            }
        }
        if (order == null) {
            return null;
        }
        if (walked.subject() != null) {
            return null;
        }
        WalkedElement.Arm one = walked.arms().getFirst();
        List<AnArmAnswered> chosen = new ArrayList<>();
        if (!armsAnswering(answer, this, new LinkedHashMap<>(one.held()), one.standing(),
                ChoicesOnTheWay.NONE, walked.elements(), ArmsEndIn.A_VALUE, chosen, symbols,
                newtypes) || chosen.size() < 2 || chosen.getFirst().taken() == null) {
            return null;
        }
        ElementProjection subject = chosen.getFirst().taken().narrowedFrom();
        List<CasesLeft> puts = new ArrayList<>();
        for (AnArmAnswered each : chosen) {
            if (each.taken() == null || !subject.equals(each.taken().narrowedFrom())
                    || !(Core.withoutStanding(each.value()) instanceof Core.Bool(
                            boolean put, var _, var _))) {
                return null;
            }
            if (put) {
                puts.add(each.taken().narrowing());
            }
        }
        return puts.isEmpty() ? null
                : new NumericTerm.GatheredUnderItsKey.Gathering.SinceAPut(subject, puts, order);
    }

    /** Each of {@code reads}, made of what stands at {@code at} in an element rather than of the
     *  element itself; a read that came to nothing stays so. */
    private static List<ReadOff> after(List<ReadOff> reads, OnePerElement.Answered at) {
        List<ReadOff> moved = new ArrayList<>();
        for (ReadOff each : reads) {
            moved.add(each == null ? null : each.after(at));
        }
        return moved;
    }

    /**
     * Which occurrences a list holds one value for each of, where each read off those values
     * stands, and the calls that kept some of them by a statement.
     */
    public sealed interface Occurrences {

        /** Where each read asked comes to, in the order asked: all of them in the one run. */
        List<Read> reads();

        /** The calls whose statements the occurrences counted must meet, outermost first, each
         *  where it stands. */
        List<Denotation> keptBy();

        /** Where a read off each value the list holds stands among the places of the input. */
        sealed interface Read {

            /** A read that comes to no place of the input. */
            Read NOWHERE = new Nowhere();

            /**
             * The place the read comes to, at every occurrence the run is over.
             *
             * @param wrapped whether the read wears the place's values as a newtype rather than
             *                being them: which are equal is kept, and nothing about their order is
             *                said
             */
            record At(TermPath place, boolean wrapped) implements Read {

                public At {
                    Objects.requireNonNull(place, "a read that comes to a place says which");
                }
            }

            /** The read takes out of a value something no place of the input holds. */
            record Nowhere() implements Read {}
        }

        /**
         * The elements of one occurrence of a container, one value each, every read standing in
         * the element of the container it was read off.
         */
        record OfOneContainer(TermPath container, List<Read> reads, List<Denotation> keptBy)
                implements Occurrences {

            public OfOneContainer {
                Objects.requireNonNull(container, "the elements of a container are a"
                        + " container's");
                reads = List.copyOf(reads);
                for (Read each : reads) {
                    if (each instanceof Read.At(TermPath place, var _)
                            && !place.isAtOrUnder(container.element())) {
                        throw new IllegalArgumentException("a read off an element of " + container
                                + " stands in that element, and " + place + " does not");
                    }
                }
                keptBy = List.copyOf(keptBy);
            }
        }

        /**
         * Every occurrence of a place inside more than one container: the lists inside the
         * elements of the container at {@code outer} put end to end.
         *
         * <p>Each read stands in an element of a list inside an element of {@code outer}, one
         * container further in than those elements and no more, as a read off an element of
         * {@link OfOneContainer} stands in that element.
         */
        record AcrossContainers(TermPath outer, List<Read> reads, List<Denotation> keptBy)
                implements Occurrences {

            public AcrossContainers {
                Objects.requireNonNull(outer, "the lists put end to end are inside the elements"
                        + " of a container");
                reads = List.copyOf(reads);
                for (Read each : reads) {
                    if (each instanceof Read.At(TermPath place, var _)
                            && !inAListInsideAnElementOf(outer, place)) {
                        throw new IllegalArgumentException("a read off an element of the lists"
                                + " inside the elements of " + outer + " stands in one of those,"
                                + " and " + place + " does not");
                    }
                }
                keptBy = List.copyOf(keptBy);
            }

            /** Whether {@code place} stands in an element of a list inside an element of the
             *  container at {@code outer}, one container further in than those elements. */
            static boolean inAListInsideAnElementOf(TermPath outer, TermPath place) {
                return place.isAtOrUnder(outer.element()) && place.containersHoldingIt().size()
                        == outer.containersHoldingIt().size() + 2;
            }
        }
    }

    /**
     * The container inside the elements of an outer one whose lists {@code list} puts end to end
     * with nothing made of an element — its elements are those of the lists — or null where the
     * list is no such flattening.
     *
     * <p>A list the closure answers some of the elements of is crossed where {@code keeping} says
     * so, and each call crossed is added to {@code keptBy}: the elements put end to end are those
     * it kept ({@link #flattenedKeysAt}).
     */
    public TermPath containerFlattenedInto(Core list, Function<Core, Core> keeping,
                                           List<Denotation> keptBy, Symbols symbols,
                                           DeclarationNewtypes newtypes) {
        Flattened elements = flattenedKeysAt(standing(list, symbols, newtypes),
                List.of(ReadOff.ITSELF), true, keeping, keptBy, symbols, newtypes);
        if (elements == null || !(elements.reads().getFirst() instanceof Occurrences.Read.At(
                TermPath keys, var _))) {
            return null;
        }
        List<TermPath> holding = keys.containersHoldingIt();
        return holding.isEmpty() ? null : holding.getLast();
    }

    /**
     * What {@code answer}, made of the element handed to {@code element}, takes out of it: a way
     * through the components of the tuples and the fields of the records it is made of, to a
     * place of it or a newtype wearing one — or null where it is none of these
     * ({@link ReadOff}).
     */
    public ReadOff readOff(Core answer, BindingId element, DeclarationNewtypes newtypes) {
        return element == null ? null : ElementProjection.readAsAKey(answer, ReadOff.ITSELF,
                element, heldByTheBody(), newtypes);
    }

    /**
     * The list a map was made from, and what each read taken out of each element of the map's
     * answer takes out of each element of that list.
     *
     * @param reads   what each read takes out of each element of the list beneath, or null where
     *                the map's answer gave it nothing to take
     * @param closure the map's closure, read where the map stands
     * @param held    what each binding of the body the closure is in holds
     */
    private record MapStep(Core from, List<ReadOff> reads, Core.Block closure,
                           Map<BindingId, Core> held) {

        /** Whether the map answered something other than each element as it is, or a newtype
         *  wearing it. Asked only where a statement or a flattening turns on it. */
        boolean madeNew(DeclarationNewtypes newtypes) {
            OnePerElement.Answered itself = OnePerElement.Answered.of(closure.body(),
                    closure.params().getFirst().binding(), held, newtypes);
            return itself == null || !itself.at().fields().isEmpty();
        }
    }

    /**
     * {@code standing}, where it is a map, looked through at what each of {@code reads} takes out
     * of each element of its answer — or null where it is no map whose closure is read here.
     *
     * <p>What the map answered may be the element, a place of it, or something built of it. Where
     * it is something built, a tuple or a record, what is taken out of it is what the map gave that
     * part of it: the construction and the read cancel ({@link ElementProjection#readAsAKey(Core,
     * ReadOff, BindingId, Map, DeclarationNewtypes)}). A read the map gave nothing to take comes to
     * nothing, and the map is crossed for the others all the same.
     */
    private MapStep throughAMap(Denotation standing, List<ReadOff> reads, Symbols symbols,
                                DeclarationNewtypes newtypes) {
        ValueName operation;
        List<Core> args;
        switch (Core.withoutStanding(standing.value())) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return null;
            }
        }
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        int mapped = built == null || built.mapsEachElementOf() == null ? -1
                : CallArguments.positionOf(built.mapsEachElementOf(), operation);
        InputReads inside = standing.at();
        Core.Block closure = mapped < 0 || mapped >= args.size() ? null
                : AnIdentityMap.closureBeside(args, mapped,
                        each -> blockOf(inside, each, symbols, newtypes));
        if (closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null) {
            return null;
        }
        BindingId element = closure.params().getFirst().binding();
        List<ReadOff> given = new ArrayList<>();
        for (ReadOff each : reads) {
            given.add(each == null ? null : ElementProjection.readAsAKey(closure.body(), each,
                    element, inside.heldByTheBody(), newtypes));
        }
        return new MapStep(args.get(mapped), given, closure, inside.heldByTheBody());
    }

    /**
     * A call putting end to end the lists its closure answered of each element of a list
     * ({@link PieceOfAnElement#WHAT_THE_CLOSURE_ANSWERS}).
     *
     * @param from    the list whose elements the closure is handed
     * @param outer   where every element of that list stands
     * @param closure the closure, read where the call stands
     */
    private record AFlattening(Core from, TermPath outer, Core.Block closure) {

        BindingId element() {
            return closure.params().getFirst().binding();
        }
    }

    /** {@code standing} as a flattening of lists its closure answered of each element of a list
     *  standing at a place of the input, or null where it is none. */
    private static AFlattening aFlattening(Denotation standing, Symbols symbols,
                                           DeclarationNewtypes newtypes) {
        ValueName operation;
        List<Core> args;
        switch (Core.withoutStanding(standing.value())) {
            case Core.Call call when call.fn() instanceof Core.Reached reached -> {
                operation = reached.denotes();
                args = call.args();
            }
            case Core.PreservedCall kept -> {
                operation = kept.declared().operation();
                args = kept.args();
            }
            default -> {
                return null;
            }
        }
        BoundOperationFacts.Assembled assembled =
                DefaultBoundOperationFacts.get().assembles(operation);
        if (assembled == null
                || assembled.piece() != PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
            return null;
        }
        int container = CallArguments.positionOf(assembled.source(), operation);
        InputReads where = standing.at();
        Core.Block closure = container < 0 || container >= args.size() ? null
                : AnIdentityMap.closureBeside(args, container,
                        each -> blockOf(where, each, symbols, newtypes));
        if (closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null
                || !(where.everyElementOf(args.get(container), newtypes)
                        instanceof PathResolution.At(TermPath outer))) {
            return null;
        }
        return new AFlattening(args.get(container), outer, closure);
    }

    /**
     * What a flattening holds where its closure answers, on every arm it is chosen by, a list
     * written with one value or with none: the one value of each element it answers one for.
     *
     * @param from          the list the flattening was made from
     * @param reads         what each read taken out of an element of the flattening takes out of
     *                      the element of {@code from} it was answered of, or null where the arms
     *                      answering a value take it out of different places
     * @param someAnswerNone whether an arm answers no value, so that the elements held are those
     *                      of {@code from} the closure answers one for
     * @param madeNew       whether a value answered is something other than the element as it is
     */
    private record OneOrNone(Core from, List<ReadOff> reads, boolean someAnswerNone,
                             boolean madeNew) {}

    /**
     * {@code standing}, where it is a flattening whose closure answers a list of one value or of
     * none on each arm it is chosen by ({@link OneOrNone}) — or null where it is not.
     *
     * <p>Such a flattening is a map of the elements it answers a value for: each of them is there
     * once, as the value its arm wrote, and the others not at all. What a read takes out of that
     * value is read off the element as a map's answer is ({@link #throughAMap}), with each name an
     * arm on the way bound standing at the case of the element it took. Which elements an arm
     * answering a value is taken for is no part of this answer: it is how many the flattening
     * holds, which the flattening's own size says.
     */
    private OneOrNone throughAFlatteningOfOneOrNone(Denotation standing, List<ReadOff> reads,
                                                    Symbols symbols,
                                                    DeclarationNewtypes newtypes) {
        AFlattening flattening = aFlattening(standing, symbols, newtypes);
        if (flattening == null) {
            return null;
        }
        BindingId element = flattening.element();
        List<AnArmAnswered> answered = new ArrayList<>();
        if (!armsAnswering(flattening.closure().body(), standing.at(),
                new LinkedHashMap<>(standing.at().heldByTheBody()), Map.of(),
                ChoicesOnTheWay.NONE, flattening.outer(), ArmsEndIn.A_LIST_OF_ONE_OR_NONE,
                answered, symbols, newtypes)) {
            return null;
        }
        List<ReadOff> given = null;
        boolean none = false;
        boolean madeNew = false;
        for (AnArmAnswered each : answered) {
            if (each.value() == null) {
                none = true;
                continue;
            }
            madeNew |= !ElementProjection.isTheElementItself(each.value(), element, each.held(),
                    newtypes);
            List<ReadOff> here = new ArrayList<>();
            for (ReadOff read : reads) {
                here.add(read == null ? null : ElementProjection.readAsAKey(each.value(), read,
                        element, each.standing(), each.held(), newtypes));
            }
            if (given == null) {
                given = here;
                continue;
            }
            for (int i = 0; i < given.size(); i++) {
                if (!Objects.equals(given.get(i), here.get(i))) {
                    given.set(i, null);
                }
            }
        }
        return given == null ? null
                : new OneOrNone(flattening.from(), given, none, madeNew);
    }

    /**
     * What one arm of a closure's answer answers: the value of the list of one it wrote, or null
     * where it wrote a list of none, with what each name on the way holds and where in the
     * element each name an arm bound stands.
     *
     * @param taken the place of the element the arm narrowed, narrowed to the cases it took, where
     *              that is the one choice on the way to the arm; null where the way made another
     *              choice or none
     */
    private record AnArmAnswered(Core value, Map<BindingId, Core> held,
                                 Map<BindingId, ElementProjection> standing,
                                 ElementProjection taken) {}

    /**
     * The choices made on the way to an arm: the case narrowing the last of them made, where it
     * made one.
     */
    private record ChoicesOnTheWay(int made, ElementProjection lastTaken) {

        static final ChoicesOnTheWay NONE = new ChoicesOnTheWay(0, null);

        ChoicesOnTheWay then(ElementProjection taken) {
            return new ChoicesOnTheWay(made + 1, taken);
        }

        /** The one choice made, where it is one and a case. */
        ElementProjection onlyCase() {
            return made == 1 ? lastTaken : null;
        }
    }

    /** What an arm of a value read by {@link #armsAnswering} ends in. */
    private enum ArmsEndIn {
        /** A list written with one value or with none: the value, or no value. */
        A_LIST_OF_ONE_OR_NONE,
        /** Whatever the arm answers, which is the value. */
        A_VALUE
    }

    /**
     * Whether {@code e}, read at {@code at}, answers on every arm it is chosen by what
     * {@code endsIn} says, each such arm added to {@code out} — through names, {@code let}s and
     * the arms of a {@code match} or an {@code if}.
     *
     * @param outer   where every element the closure is handed stands, which a name an arm on the
     *                way bound stands inside
     * @param choices the choices made on the way to {@code e}
     */
    private static boolean armsAnswering(Core e, InputReads at, Map<BindingId, Core> held,
                                         Map<BindingId, ElementProjection> standing,
                                         ChoicesOnTheWay choices, TermPath outer, ArmsEndIn endsIn,
                                         List<AnArmAnswered> out, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        Denotation made = at.standing(e, symbols, newtypes);
        InputReads there = made.at();
        return switch (Core.withoutStanding(made.value())) {
            case Core.ListLit written when endsIn == ArmsEndIn.A_LIST_OF_ONE_OR_NONE
                    && written.elements().size() <= 1 -> {
                out.add(new AnArmAnswered(written.elements().isEmpty() ? null
                        : written.elements().getFirst(), Map.copyOf(held), standing,
                        choices.onlyCase()));
                yield true;
            }
            case Core.LetIn let when let.binder() != null && let.binder().binding() != null -> {
                held.put(let.binder().binding(), let.value());
                yield armsAnswering(let.body(), there.and(let.binder(), let.value()), held,
                        standing, choices, outer, endsIn, out, symbols, newtypes);
            }
            // A name the body gave a choice is that choice: what stands for one value stands as
            // the name, and the arms are read where it was written.
            case Core.Read name when held.get(name.binding()) instanceof Core given
                    && Core.withoutStanding(given) instanceof Core.Match ->
                    armsAnswering(given, there, held, standing, choices, outer, endsIn, out,
                            symbols, newtypes);
            case Core.Match match -> everyCaseAnswers(match, there, held, standing, choices,
                    outer, endsIn, out, symbols, newtypes);
            // A condition chooses by no case of the element and binds no name.
            case Core.If iff -> {
                for (Choice.Arm arm : Choice.of(iff).arms()) {
                    if (!armsAnswering(arm.answers(),
                            there.choosing(arm.decidedBy(), symbols, newtypes), held, standing,
                            choices.then(null), outer, endsIn, out, symbols, newtypes)) {
                        yield false;
                    }
                }
                yield true;
            }
            case Core value when endsIn == ArmsEndIn.A_VALUE -> {
                out.add(new AnArmAnswered(value, Map.copyOf(held), standing,
                        choices.onlyCase()));
                yield true;
            }
            case Core value when AnOperationApplied.of(value) instanceof AnOperationApplied(
                    ValueName operation, List<Core> args) -> aMapOfOneOrNone(operation, args,
                    there, held, standing, choices, outer, out, symbols, newtypes);
            default -> false;
        };
    }

    /**
     * Whether every arm of {@code match} answers what {@code endsIn} says, each arm read where
     * choosing it puts the reading — which is this reading's own answer ({@link #choosing}) — and
     * the name it binds standing at the place it narrowed, inside the element.
     */
    private static boolean everyCaseAnswers(Core.Match match, InputReads there,
                                            Map<BindingId, Core> held,
                                            Map<BindingId, ElementProjection> standing,
                                            ChoicesOnTheWay choices, TermPath outer,
                                            ArmsEndIn endsIn, List<AnArmAnswered> out,
                                            Symbols symbols, DeclarationNewtypes newtypes) {
        for (Core.Case taken : match.cases()) {
            InputReads inside = there.choosing(Choice.Decides.ofCase(match, taken), symbols,
                    newtypes);
            Map<BindingId, ElementProjection> bound = standing;
            ElementProjection narrowed = null;
            if (taken.binder() != null && taken.binder().binding() != null) {
                if (!(inside.names.roleOf(taken.binder().binding())
                        instanceof BindingRole.Root(TermPath path))
                        || !(ElementProjection.below(outer, path)
                                instanceof ElementProjection projection)) {
                    return false;
                }
                Map<BindingId, ElementProjection> wider = new LinkedHashMap<>(standing);
                wider.put(taken.binder().binding(), projection);
                bound = Map.copyOf(wider);
                narrowed = projection.narrowing() == null ? null : projection;
            }
            if (!armsAnswering(taken.body(), inside, held, bound, choices.then(narrowed),
                    outer, endsIn, out, symbols, newtypes)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Whether {@code operation} applied to {@code args} is a map of a list of one value or none,
     * which is a list of one or none of what its closure answers of that value — each such answer
     * added to {@code out}.
     */
    private static boolean aMapOfOneOrNone(ValueName operation, List<Core> args, InputReads there,
                                           Map<BindingId, Core> held,
                                           Map<BindingId, ElementProjection> standing,
                                           ChoicesOnTheWay choices, TermPath outer,
                                           List<AnArmAnswered> out, Symbols symbols,
                                           DeclarationNewtypes newtypes) {
        BuiltFrom<DeclaredArgument> built =
                DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
        int mapped = built == null || built.mapsEachElementOf() == null ? -1
                : CallArguments.positionOf(built.mapsEachElementOf(), operation);
        Core.Block closure = mapped < 0 || mapped >= args.size() ? null
                : AnIdentityMap.closureBeside(args, mapped,
                        each -> blockOf(there, each, symbols, newtypes));
        if (closure == null || closure.params().size() != 1
                || closure.params().getFirst().binding() == null) {
            return false;
        }
        List<AnArmAnswered> given = new ArrayList<>();
        if (!armsAnswering(args.get(mapped), there, held, standing, choices, outer,
                ArmsEndIn.A_LIST_OF_ONE_OR_NONE, given, symbols, newtypes)) {
            return false;
        }
        for (AnArmAnswered each : given) {
            if (each.value() == null) {
                out.add(each);
                continue;
            }
            Map<BindingId, Core> handed = new LinkedHashMap<>(each.held());
            handed.put(closure.params().getFirst().binding(), each.value());
            out.add(new AnArmAnswered(closure.body(), Map.copyOf(handed), each.standing(),
                    each.taken()));
        }
        return true;
    }

    /**
     * Where the keys of a list a flattening put end to end stand: inside the container whose
     * elements the closure was handed, at the place the closure's answer is read down to — or
     * null where that is no list inside each of those elements, one container further in.
     *
     * <p>A list the closure answers some of the elements of, by an operation keeping them by a
     * statement, is crossed where {@code keeping} says so, and the call is added to
     * {@code keptBy}: what it keeps by is about an element of a list inside the one element the
     * closure was handed, which is one of the elements put end to end.
     *
     * @param ofTheListsThemselves whether the elements must be those of the lists the closure
     *                             answers, the answer being read down no steps that make a value
     *                             of one
     * @param keeping              the list a call keeps some of the elements of by a statement, or
     *                             null where the call is no such operation — or null itself,
     *                             where no such call is crossed
     * @param keptBy               where each call crossed so is added, as it stands
     */
    private Flattened flattenedKeysAt(Denotation standing, List<ReadOff> reads,
                                      boolean ofTheListsThemselves,
                                      Function<Core, Core> keeping, List<Denotation> keptBy,
                                      Symbols symbols, DeclarationNewtypes newtypes) {
        AFlattening flattening = aFlattening(standing, symbols, newtypes);
        if (flattening == null) {
            return null;
        }
        InputReads where = standing.at();
        TermPath outer = flattening.outer();
        BindingId element = flattening.element();
        Core answer = flattening.closure().body();
        ElementProjection listAt = ElementProjection.read(answer, element, where.heldByTheBody(),
                newtypes);
        List<ReadOff> sought = new ArrayList<>(reads);
        // A list is read down to a place of the element a step at a time. Each step goes to a part
        // of what the answer stands as, and a name followed there to what it was bound to, so the
        // walk stays inside one finite tree; a node come round to again is one already answered.
        Set<Core> met = Collections.newSetFromMap(new IdentityHashMap<>());
        while (listAt == null) {
            if (!met.add(answer)) {
                return null;
            }
            Denotation here = where.standing(answer, symbols, newtypes);
            Core beneathKept = keeping == null ? null : keeping.apply(here.value());
            if (beneathKept != null) {
                keptBy.add(here);
                answer = beneathKept;
                listAt = ElementProjection.read(answer, element, where.heldByTheBody(), newtypes);
                continue;
            }
            MapStep mapped = throughAMap(here, sought, symbols, newtypes);
            if (mapped != null) {
                if (ofTheListsThemselves && mapped.madeNew(newtypes)) {
                    return null;
                }
                sought = mapped.reads();
                answer = mapped.from();
                listAt = ElementProjection.read(answer, element, where.heldByTheBody(), newtypes);
                continue;
            }
            InputPath.Beneath step = InputPath.oneStepBeneath(answer,
                    ElementQuestion.ONE_PER_ELEMENT, where.names(), newtypes,
                    each -> blockOf(where, each, symbols, newtypes));
            if (step == null
                    || (ofTheListsThemselves && !step.answered().at().fields().isEmpty())) {
                return null;
            }
            sought = after(sought, step.answered());
            answer = step.from();
            listAt = ElementProjection.read(answer, element, where.heldByTheBody(), newtypes);
        }
        TermPath elementsOfTheLists = listAt.from(outer).element();
        List<TermPath> holdingTheElements = outer.containersHoldingIt();
        TermPath container = holdingTheElements.isEmpty() ? null : holdingTheElements.getLast();
        return container != null
                && Occurrences.AcrossContainers.inAListInsideAnElementOf(container,
                        elementsOfTheLists)
                ? new Flattened(container, placedIn(sought, elementsOfTheLists)) : null;
    }

    /** What {@link #flattenedKeysAt} found: the container whose elements hold the lists, and
     *  where each read stands in the lists' elements. */
    private record Flattened(TermPath outer, List<Occurrences.Read> reads) {}

    /** Where each of {@code reads}, taken out of the value at {@code element}, stands. */
    private static List<Occurrences.Read> placedIn(List<ReadOff> reads, TermPath element) {
        List<Occurrences.Read> placed = new ArrayList<>();
        for (ReadOff each : reads) {
            OnePerElement.Answered at = each == null ? null : each.placed();
            placed.add(at == null ? Occurrences.Read.NOWHERE
                    : new Occurrences.Read.At(at.at().from(element), at.wrapped()));
        }
        return placed;
    }

    private static Core.Block blockOf(InputReads at, Core closure, Symbols symbols,
                                      DeclarationNewtypes newtypes) {
        return Core.withoutStanding(at.standing(closure, symbols, newtypes).value())
                instanceof Core.Block block ? block : null;
    }

    /**
     * The position of the container of the input {@code list}, read here, holds something exactly
     * where it does, or no position where there is none ({@link ElementQuestion#SAME_EMPTINESS}).
     */
    public PathResolution holdingSomethingWhere(Core list, Symbols symbols,
                                                DeclarationNewtypes newtypes) {
        Core asked = list;
        Denotation at = standing(list, symbols, newtypes);
        // A step to a name is a step over the binding graph, and a name come round to again is one
        // already answered for; a step down an operation stays inside one finite tree.
        Set<BindingId> met = new HashSet<>();
        while (true) {
            // Asked of the list as handed to the step and as it came to be reached, since
            // following names sets aside what a value stood as on the way.
            if (!InputPath.goesOnThrough(asked, at.value(), ElementQuestion.SAME_EMPTINESS)) {
                return new PathResolution.NotAPosition();
            }
            if (at.at().pathOf(at.value(), newtypes) instanceof PathResolution.At(
                    TermPath container)) {
                return new PathResolution.At(container);
            }
            if (Core.withoutStanding(at.value()) instanceof Core.Read name
                    && !met.add(name.binding())) {
                return new PathResolution.NotAPosition();
            }
            InputReads where = at.at();
            InputPath.Beneath step = InputPath.oneStepBeneath(at.value(),
                    ElementQuestion.SAME_EMPTINESS, where.names(), newtypes,
                    closure -> blockOf(where, closure, symbols, newtypes));
            if (step == null) {
                return new PathResolution.NotAPosition();
            }
            asked = step.from();
            at = where.standing(asked, symbols, newtypes);
        }
    }

    /** What the walk handing {@code binding} its element answered, as the closure, where a licence
     *  says it answered one value per element ({@link ElementAnswer}). */
    public ElementAnswer answerAt(BindingId binding) {
        return names.answerAt(binding);
    }

    /** What each binding of the body holds, for reading a closure's answer through the names in it. */
    Map<BindingId, Core> heldByTheBody() {
        return names.heldByTheBody();
    }

    /** What the declarations put at each position of the input this reads, which is what an arm
     *  of a {@code match} on a place of it asks whether it narrows ({@link #insideArmOn}). */
    DeclaredInput declared() {
        return declared;
    }

    /**
     * What {@code read}'s name stands for here ({@link ReadMeaning}).
     *
     * <p>The one place a name is given a meaning for this side, and the whole of what this reading
     * knows about one. Every reader that meets a name asks here — the arithmetic that finds the line
     * a rule draws, and the walk that says which positions a rule mentions — so the two agree about
     * what a name is rather than each working out what a missing position meant.
     *
     * <p>A position first, and by whichever road reaches one. That is not the same as asking whether
     * the binding is a parameter: a name an operation handed an element on stands at a position
     * wherever its container does, and so does one bound to something that names a position. So what
     * is asked first is the whole walk after a position ({@link InputPath}) rather than one of the
     * facts it is built from.
     *
     * <p>Then a set the arms already narrowed, which is the same order as everywhere else: what is in
     * force where the name is read wins over what was true of it further out.
     *
     * <p>And what is left is read from where the binding came from ({@link BindingRole}), which is
     * the one place those facts are ordered. Nothing is re-ordered here — the walk after a position
     * reads the same ordering, so a name that got past it is one no road placed, and what remains is
     * to say which kind of value it has.
     *
     * <p>What it holds is answered last and only as the expression. Whether that expression may
     * stand where the name does is the caller's question, asked of the fact rather than of a
     * permission recorded here: an arithmetic reader substitutes it, and a reader collecting
     * positions walks into it, and neither is the other's rule.
     */
    public ReadMeaning meaningOf(Core.Read read, Symbols symbols, DeclarationNewtypes newtypes) {
        return meaningOf(read, symbols, newtypes, new HashSet<>());
    }

    /**
     * {@code e} followed through the calls that handed it over, and nothing else: a parameter of a
     * body a call entered is the value the call handed it, read where the call stands, and that
     * value is followed in turn if it is one too.
     *
     * <p>Beside {@link #denotes}, which goes on through whatever a name stands for, an element of
     * what a walk answered included. A reader asking which container a name is an element of
     * needs the name that is one, and past it is the walk's answer, which is no longer an element.
     */
    public Denotation handedOver(Core e) {
        Core at = Core.withoutStanding(e);
        InputReads reads = this;
        Set<BindingId> met = new HashSet<>();
        while (at instanceof Core.Read read && met.add(read.binding())) {
            if (reads.applied.given().get(read.binding()) instanceof Denotation given) {
                at = Core.withoutStanding(given.value());
                reads = given.at();
            } else if (reads.names.roleOf(read.binding()) instanceof BindingRole.Alias(var value)) {
                at = Core.withoutStanding(value);
            } else {
                break;
            }
        }
        return new Denotation(at, reads);
    }

    /**
     * What {@code e} stands for, through however many names were given to it.
     *
     * <p>A name is a name and not another value: a closure bound once and read under a second name
     * is the same closure, and a walk that stopped at the first read would answer one thing for
     * {@code List.sum(List.map(f, xs))} and another for the same model with a name in the middle —
     * which is a {@code let} changing what a model means.
     *
     * <p>Here because {@link #meaningOf} is here. What a name stands for is this reading's answer,
     * and a caller that followed the chain for itself would be a second walk of it — three of them
     * were, each stopping where its own caller needed and each free to learn a shape the others
     * did not.
     *
     * <p>What comes back is the expression and the reading it is under, because the second is not
     * the one the name was read in: a name bound inside a helper stands for what the call handed
     * over, and what is read of that afterwards is read where it stands. Handed the expression
     * alone, a caller goes on asking the outer reading about a value that is not in it.
     *
     * <p>It is never a permission. Whether the expression may stand where the name did is the
     * caller's question, and so is what kind of expression it wanted: a reader after a closure
     * takes a block from this and one after a walk takes whatever is there.
     *
     * <p>By the bindings met, which is what makes it stop. Each tells itself from every other, so a
     * name that came round to itself is one already answered for, and what is handed back is the
     * name rather than a walk that does not end.
     */
    public Denotation denotes(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        // Which expression a name stands for does not turn on the type it stands as there.
        Core at = Core.withoutStanding(e);
        InputReads reads = this;
        Set<BindingId> met = new HashSet<>();
        while (at instanceof Core.Read read) {
            if (!met.add(read.binding())
                    || !(reads.meaningOf(read, symbols, newtypes)
                            instanceof ReadMeaning.Through through)) {
                return new Denotation(at, reads);
            }
            at = Core.withoutStanding(through.denotes().value());
            reads = through.denotes().at();
        }
        return new Denotation(at, reads);
    }

    /**
     * The map {@code lookup}, read here, looks a key up in, read where it stands — where the key
     * is one of that same map's keys; or null where {@code lookup} is no lookup in a map, or the
     * key is not shown to be one of the map's.
     *
     * <p>The key is one of the map's where it is an element handed from a list of the map's keys,
     * or from a list holding only elements of such a list: the step down to the list an element
     * was handed from is the one every reader following an element back takes
     * ({@link #holdingTheElementsOf}).
     *
     * <p>And the map whose keys were listed is the map looked in where the two are one value by
     * name ({@link #oneNamedValue}). Two maps written alike are two maps here, whatever they hold:
     * what is asked is that the lookup finds an entry, and only one value is known to have one.
     */
    public Denotation mapLookedUpUnderOneOfItsOwnKeys(Core lookup, Symbols symbols,
                                                      DeclarationNewtypes newtypes) {
        if (!(AnOperationApplied.of(lookup) instanceof AnOperationApplied looked)
                || !GET.equals(looked.operation()) || looked.args().size() != 2) {
            return null;
        }
        Denotation key = standing(looked.args().getFirst(), symbols, newtypes);
        Core handedFrom = key.at().containerOfTheElement(key.value());
        if (handedFrom == null) {
            return null;
        }
        Denotation listing = key.at().standing(handedFrom, symbols, newtypes);
        Denotation keysOf = mapWhoseKeysAreListedBy(listing, symbols, newtypes);
        Denotation map = new Denotation(looked.args().get(1), this);
        return keysOf != null && oneNamedValue(keysOf, map, symbols, newtypes)
                ? standing(map.value(), symbols, newtypes) : null;
    }

    /**
     * The map {@code list}, read where it stands, lists the keys of beneath every operation
     * holding only elements of what it was handed — the map as it was handed to the listing,
     * not read past its name — or null where it lists no map's keys.
     */
    private Denotation mapWhoseKeysAreListedBy(Denotation list, Symbols symbols,
                                               DeclarationNewtypes newtypes) {
        Denotation at = list;
        while (at != null) {
            AnOperationApplied applied = AnOperationApplied.of(at.value());
            BoundOperationFacts.Listed listed = applied == null ? null
                    : DefaultBoundOperationFacts.get().listsAPartOf(applied.operation());
            if (listed != null) {
                return listed.part() == MapPart.KEYS
                        ? new Denotation(applied.argument(listed.map()), at.at()) : null;
            }
            at = oneStepBeneath(at, symbols, newtypes, (operation, args, where) ->
                    holdingTheElementsOf(operation, args, where, symbols, newtypes));
        }
        return null;
    }

    /**
     * Whether {@code one} and {@code other} are one value by name: the names each is read
     * through, followed as {@link #denotes} follows them, come to one binding.
     *
     * <p>Asked only of names read in one reading of one rule, both from where a lookup stands
     * ({@link #mapLookedUpUnderOneOfItsOwnKeys}). There a binding is one value: a helper is expanded
     * at each call with bindings of its own, and a body a reading enters binds its parameters to
     * the one call it entered for. A binding met on both ways is the same binding holding the same
     * value, and two calls written alike meet at none.
     */
    private static boolean oneNamedValue(Denotation one, Denotation other, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        Set<BindingId> named = namesFollowed(one, symbols, newtypes);
        return namesFollowed(other, symbols, newtypes).stream().anyMatch(named::contains);
    }

    /** The names {@code from} is read through on the way to what it denotes, itself first. */
    private static Set<BindingId> namesFollowed(Denotation from, Symbols symbols,
                                                DeclarationNewtypes newtypes) {
        Core at = Core.withoutStanding(from.value());
        InputReads reads = from.at();
        Set<BindingId> met = new LinkedHashSet<>();
        while (at instanceof Core.Read read && met.add(read.binding())
                && reads.meaningOf(read, symbols, newtypes)
                        instanceof ReadMeaning.Through through) {
            at = Core.withoutStanding(through.denotes().value());
            reads = through.denotes().at();
        }
        return met;
    }

    /**
     * Whether {@code e} is a value the source wrote out all the way down, read here — which is a
     * value the same every time.
     *
     * <p>A written value, one built out of written values, and a name that stands for one: the one
     * value it denotes, or every value it can take where those are written down
     * ({@link ReadMeaning.OneOf}). The last is what a closure handed the elements of a list written
     * out is handed, so what it applies to its parameter is applied to a written value — and it is
     * here and not with a reader of the closure because what a name stands for is this reading's
     * answer. A reader that kept its own account of which names are written would be a second
     * answer, and one that knew it only for the closure it happened to be walking would read the
     * same name two ways.
     *
     * <p>A list is written out only where every element is: a list holding a position is a list of
     * that position's values.
     */
    public boolean writtenOut(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return writtenOut(new Denotation(e, this), true, symbols, newtypes, new HashSet<>());
    }

    /**
     * Whether {@code e} is one value the source wrote out all the way down, read here.
     *
     * <p>{@link #writtenOut} with a name that stands for every value of several left out, at any
     * depth. Each of those values is written, and still the name is one of them on one run and
     * another on the next: what it holds is not one value, whatever each value is.
     */
    public boolean writtenOutAsOneValue(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return writtenOut(new Denotation(e, this), false, symbols, newtypes, new HashSet<>());
    }

    private static boolean writtenOut(Denotation from, boolean ofSeveral, Symbols symbols,
                                      DeclarationNewtypes newtypes, Set<BindingId> met) {
        Denotation at = standing(from, symbols, newtypes, met);
        InputReads reads = at.at();
        return switch (Core.withoutStanding(at.value())) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _, Core.OptionNone _ -> true;
            case Core.Read name -> ofSeveral
                    && reads.meaningOf(name, symbols, newtypes, new HashSet<>(met))
                            instanceof ReadMeaning.OneOf one
                    && one.everyValueItMayBe().stream()
                            .allMatch(each -> writtenOut(each, true, symbols, newtypes,
                                    new HashSet<>(met)));
            case Core.Neg negated -> writtenOut(new Denotation(negated.operand(), reads),
                    ofSeveral, symbols, newtypes, new HashSet<>(met));
            case Core.OptionSome some -> writtenOut(new Denotation(some.value(), reads),
                    ofSeveral, symbols, newtypes, new HashSet<>(met));
            case Core.ListLit list -> list.elements().stream()
                    .allMatch(each -> writtenOut(new Denotation(each, reads), ofSeveral, symbols,
                            newtypes, new HashSet<>(met)));
            case Core.Tuple tuple -> tuple.elements().stream()
                    .allMatch(each -> writtenOut(new Denotation(each, reads), ofSeveral, symbols,
                            newtypes, new HashSet<>(met)));
            case Core.Construct made -> made.values().stream()
                    .allMatch(each -> writtenOut(new Denotation(each.value(), reads), ofSeveral,
                            symbols, newtypes, new HashSet<>(met)));
            case null, default -> false;
        };
    }

    /**
     * The same, through the bindings a walk into a container has already met.
     *
     * <p>One set for the whole answer, because the answer reaches back into this: a name an
     * operation handed an element on is answered by walking to the container it came from, and that
     * walk meets names this has to answer about. Threaded rather than started afresh at each step,
     * so what stops the walk is the bindings met and not a depth anybody chose.
     */
    private ReadMeaning meaningOf(Core.Read read, Symbols symbols, DeclarationNewtypes newtypes,
                                  Set<BindingId> met) {
        // A name is what it stands at where it stands at one, and where it stands at none the
        // answers below say what else it is.
        switch (pathOf(read, newtypes)) {
            case PathResolution.At(var at) -> {
                return new ReadMeaning.Position(at);
            }
            case PathResolution.NotAPosition _ -> { }
            // A name that only may stand at a position is not the name of one, and what it is
            // instead is what the answers below say — an element, which is what it is however many
            // containers it is an element of.
            case PathResolution.MayStandAt _, PathResolution.MadeOf _ -> { }
        }
        // What a call handed a parameter of the body it entered, read where the call stands.
        Denotation given = applied.given().get(read.binding());
        if (given != null) {
            // What this reading took goes with a value read where it was given, and not into a
            // definition, which is read where nothing taken on the way here is.
            Denotation defined = definedAs(given.value(), given.at());
            return new ReadMeaning.Through(defined != null ? defined
                    : carryingWhatIsTaken(given));
        }
        List<ReadMeaning.Occurrence> narrowed = alternatives.get(read.binding());
        if (narrowed != null) {
            return new ReadMeaning.OneOf(narrowed.stream().map(this::carryingWhatIsTaken)
                    .toList());
        }
        return switch (names.roleOf(read.binding())) {
            // What a container written out holds is the occurrences that walk writes out
            // ({@link WrittenOutElements}), and what a walk answering one value per element of a
            // container it cannot write out holds is that walk's answer on one of them. A map's
            // keys are among neither, so a key is a key of the map and which one is not said.
            case BindingRole.Element(var held) -> {
                if (held.part() != HeldIn.Part.ELEMENT) {
                    yield new ReadMeaning.Element();
                }
                Denotation container = standing(new Denotation(held.container(), this), symbols,
                        newtypes, met);
                switch (WrittenOutElements.of(container, symbols, newtypes, met)) {
                    // No element at all, which is an answer of its own and not a set of none.
                    case WrittenOutElements.Walked.Each each when each.asWritten().isEmpty() -> {
                        yield new ReadMeaning.NoneHeld();
                    }
                    case WrittenOutElements.Walked.Each each -> {
                        yield new ReadMeaning.OneOf(each.asWritten());
                    }
                    case WrittenOutElements.Walked.PastTheFigure _ -> {
                        yield new ReadMeaning.MoreThanAreWrittenOut();
                    }
                    case WrittenOutElements.Walked.NotWrittenOut _ -> { }
                }
                ReadMeaning answered = answerOnEachElement(container, symbols, newtypes, met);
                yield answered == null ? new ReadMeaning.Element() : answered;
            }
            // An element of more than one container is an element, and what it may be is not the
            // values of any one of them. Answered with what one container was written with, a name
            // would stand for a value out of a container the run it is on never walked; answered
            // with what all of them were, it would stand for a set no run puts there.
            case BindingRole.ElementOfSeveral _ -> new ReadMeaning.Element();
            // Read in this environment. Bindings are added on the way down and each tells itself
            // from every other, so what was bound after this name does not answer for what it holds
            // — which is why the environment at the binder and the one at the read cannot be told
            // apart yet. Said once here rather than by each reader, so the day they can be, one
            // place changes.
            //
            // A name bound to the very read being answered is a name this knows nothing about: the
            // value would be the question, and a reader handed it would ask it again.
            case BindingRole.Alias(var value) -> value == read ? new ReadMeaning.Unknown()
                    : new ReadMeaning.Through(denoting(value, this));
            case BindingRole.Unknown _ -> new ReadMeaning.Unknown();
            // A parameter is the position it is the name of. The walk above reaches it by the same
            // fact, so nothing gets here — and what would be said if anything did is what is said
            // there, rather than a failure invented to fill the arm.
            case BindingRole.Root(var at) -> new ReadMeaning.Position(at);
        };
    }

    /**
     * The elements a container standing as {@code standing} was written with, or null where it was
     * not written out.
     *
     * <p>What makes this an answer about every element and not about some of them is that the
     * container was followed only through steps with one successor ({@link #standing}) — a name
     * this environment bound, and the body of a binding — and a list written in the source is what
     * stands there. An operation that builds a container answers elements this walk cannot
     * enumerate, and the walk stops rather than reading what went in: {@code List.append(xs, ys)}
     * holds the elements of both, and a reading that took either would have written out a set
     * missing the other half.
     *
     * <p><b>Followed with this environment and never with the body's.</b> What a binding holds is
     * also recorded over the whole body ({@link ElementBindings#boundTo}), and
     * reading a container out of that would give a value with no environment to read it in — after
     * which the environment each element is read in would be whichever one the caller had in hand.
     * Where the way to the list runs through a binding this walk has not passed, the elements are
     * not written out, and that is a capability short of what a reader could have rather than a set
     * put together out of two readings.
     *
     * <p>Null for a list written empty. No value stands at an element of it, so there is nothing for
     * a statement about every member to be about, and a statement quantified over no members holds
     * whatever it says.
     */
    private static java.util.List<Denotation> writtenElementsOf(Denotation standing) {
        if (!(Core.withoutStanding(standing.value()) instanceof Core.ListLit written)
                || written.elements().isEmpty()) {
            return null;
        }
        java.util.List<Denotation> out = new java.util.ArrayList<>();
        // Which value each member is does not turn on the type it stands as in the list.
        written.elements().forEach(each ->
                out.add(new Denotation(Core.withoutStanding(each), standing.at())));
        return out;
    }

    /**
     * What a container standing as {@code standing} holds at each element, where it is the answers
     * of one walk, one for each element of what that walk was handed — or null where it is not.
     *
     * <p>The step's body, read where the walk stands, with the step's parameter standing for the
     * element it was handed. {@code List.map(x -> x + 1, xs)} holds {@code x + 1} for each element
     * of {@code xs}, so a rule about one of its elements is a rule about {@code x + 1}, and what
     * {@code x} is is the reading's question like any other name's.
     *
     * <p>The walk this container is and not one over the same elements. Two walks over {@code xs}
     * answer different values, so which step's body an element is is read off the application that
     * built the container ({@link ElementBindings#stepAnsweredOnEachElement}), and where that
     * application answers no run of one value per element — a {@code filter} keeps some of them, a
     * set's {@code map} may answer one value for two — the element is an element and nothing more.
     *
     * <p>Read in the environment the walk stands in. A name the step's body reads from outside it
     * was bound above the walk, and what it stands for there is what the step was applied under.
     *
     * <p>And where what the walk was handed was written out, each element is the step's answer on
     * one of the values it was written with — one of several, each read on the application handing
     * the step that value ({@link ReadMeaning.OneOf}), as an element of the written list itself is.
     */
    private static ReadMeaning answerOnEachElement(Denotation standing, Symbols symbols,
                                                   DeclarationNewtypes newtypes,
                                                   Set<BindingId> met) {
        AnsweredByAWalk answered = answeredByAWalk(standing, symbols, newtypes, met);
        if (answered != null) {
            return answered.meaning();
        }
        ReadMeaning component = componentOfAnAnsweredElement(standing, symbols, newtypes, met);
        return component != null ? component
                : insideTheListsAnswered(standing, symbols, newtypes, met);
    }

    /**
     * What a container put together of the lists a step answered holds at each element, where
     * every list the step answers is written with the one element — or null where it is not so
     * put together.
     *
     * <p>{@code List.flatMap(x -> if keep(x) then [f(x)] else [], xs)} holds {@code f(x)} for the
     * elements of {@code xs} it keeps, so a rule about one of its elements is a rule about
     * {@code f(x)}, as for a {@code List.map} that answers {@code f(x)} for each. Which elements
     * are kept is not said, and a rule about the element holds of the kept ones only.
     */
    private static ReadMeaning insideTheListsAnswered(Denotation standing, Symbols symbols,
                                                      DeclarationNewtypes newtypes,
                                                      Set<BindingId> met) {
        InputReads at = standing.at();
        ElementBindings.PiecesOfEachElement pieces = ElementBindings.piecesOfEachElement(
                standing.value(), closure -> Core.withoutStanding(
                        standing(new Denotation(closure, at), symbols, newtypes, met).value())
                        instanceof Core.Block block ? block : null);
        if (pieces == null || pieces.piece() != PieceOfAnElement.WHAT_THE_CLOSURE_ANSWERS) {
            return null;
        }
        Core element = ElementBindings.theOneElementWritten(pieces.step().body());
        return element == null ? null : new ReadMeaning.Through(new Denotation(element, at));
    }

    /** What a walk's answers are read as, and the walk that answered them. */
    private record AnsweredByAWalk(ElementBindings.StepOnEachElement walk, ReadMeaning meaning) {}

    /** {@link #answerOnEachElement} for a container that is one walk's answers, or null where it
     *  is not one. */
    private static AnsweredByAWalk answeredByAWalk(Denotation standing, Symbols symbols,
                                                   DeclarationNewtypes newtypes,
                                                   Set<BindingId> met) {
        InputReads at = standing.at();
        ElementBindings.StepOnEachElement walk = ElementBindings.stepAnsweredOnEachElement(
                standing.value(), closure -> Core.withoutStanding(
                        standing(new Denotation(closure, at), symbols, newtypes, met).value())
                        instanceof Core.Block block ? block : null);
        if (walk == null) {
            return null;
        }
        List<Denotation> walked = walk.element() == null
                || walk.element().binding() == null ? null
                : writtenElementsOf(standing(new Denotation(walk.walked(), at), symbols, newtypes,
                        new HashSet<>(met)));
        if (walked == null) {
            return new AnsweredByAWalk(walk,
                    new ReadMeaning.Through(new Denotation(walk.step().body(), at)));
        }
        List<Denotation> each = new ArrayList<>();
        for (Denotation value : walked) {
            each.add(new Denotation(walk.step().body(),
                    at.handing(walk.element().binding(), value, newtypes)));
        }
        return new AnsweredByAWalk(walk, ReadMeaning.OneOf.ofEvery(each));
    }

    /**
     * The component {@code standing} holds at each element, where it is a component of the tuples
     * a walk answered, or null where it is not.
     *
     * <p>{@code Map.fromList(List.map(x -> (x, 1), xs))} holds {@code 1}: each value is the second
     * component of an entry, and the entry is what the step answered on an element. Some entry and
     * not each, since a key filed twice keeps the later value; so what this licenses is where a
     * value came from, which is all the reading of an element asks.
     *
     * <p>Only where the entries are one step's answer on an element, and where that value is no
     * less the value of the entry that is left. Entries filed under one key leave the last, so a
     * value an earlier entry carried is compared with nothing, and a line drawn on it would be met
     * by a row that never runs the comparison there. What makes the loss harmless is that entries
     * under one key carry one value ({@link #fixedByTheKey}); where that is not shown the element
     * is an element. Entries written out would make each value one of the components written, and
     * the one left is only some of them, so a list of alternatives would name values the map does
     * not hold.
     */
    private static ReadMeaning componentOfAnAnsweredElement(Denotation standing, Symbols symbols,
                                                            DeclarationNewtypes newtypes,
                                                            Set<BindingId> met) {
        ElementBindings.Projection part = ElementBindings.componentOfTheElementsOf(
                standing.value());
        if (part == null) {
            return null;
        }
        Denotation entries = standing(new Denotation(part.of(), standing.at()), symbols, newtypes,
                met);
        AnsweredByAWalk answered = answeredByAWalk(entries, symbols, newtypes, met);
        if (answered == null || !(answered.meaning() instanceof ReadMeaning.Through through)
                || answered.walk().element() == null
                || answered.walk().element().binding() == null) {
            return null;
        }
        Denotation written = standing(through.denotes(), symbols, newtypes, met);
        if (!(Core.withoutStanding(written.value()) instanceof Core.Tuple tuple)
                || Math.max(part.index(), part.filedUnder()) >= tuple.elements().size()) {
            return null;
        }
        Core value = tuple.elements().get(part.index());
        return fixedByTheKey(tuple.elements().get(part.filedUnder()), value,
                answered.walk().element().binding(), written.at())
                ? new ReadMeaning.Through(new Denotation(value, written.at())) : null;
    }

    /**
     * Whether two entries of one walk that are filed under the same key carry the same value, so
     * that the entry which is left holds what the one it replaced held.
     *
     * <p>Shown for the two forms that need no argument about the step: a value that does not read
     * the element at all, which is one value whichever element it is, and a value that reads only
     * the element where the key is that element itself, so that entries under one key are entries
     * of equal elements. Every name the value reads is the element, or a parameter of the
     * behavior, which is the same one for every element. Whatever else it reads — a name bound in
     * the step, or by a let above it — is a name this does not know to be one value per key, and
     * the answer is no.
     */
    private static boolean fixedByTheKey(Core key, Core value, BindingId element,
                                         InputReads at) {
        boolean keyIsTheElement = Core.withoutStanding(key) instanceof Core.Read read
                && read.binding().equals(element);
        Set<BindingId> made = new HashSet<>();
        Set<BindingId> read = new HashSet<>();
        walkNames(value, made, read);
        read.removeAll(made);
        return read.stream().allMatch(binding -> (keyIsTheElement && binding.equals(element))
                || at.names.roleOf(binding) instanceof BindingRole.Root);
    }

    /**
     * What {@code e} stands as here: followed through every name that stands for one value and
     * every binding whose body is the value, and read in the names in force where it ends.
     *
     * <p>Beside {@link #denotes}, which follows names alone. A helper the source called stands as
     * the binding of its parameters around its body, so what a call to one stands as is past a
     * binding a walk after names stops at.
     */
    public Denotation standing(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return standing(new Denotation(e, this), symbols, newtypes, new HashSet<>());
    }

    /**
     * What the name {@code e} was bound to here, followed no further: the one value it stands for;
     * none where {@code e} is not a name, or is one standing for something of its own.
     *
     * <p>Every value a name is one of is answered where the environment has them, so that a
     * reader asking what a use runs asks it of each. This environment keeps none
     * ({@link ValueStanding.Names#alternativesOf}), and a name is one value or none.
     *
     * <p>Beside {@link #standing}, which follows the name on to where it ends. What was run to
     * work the bound value out is run whatever the name goes on to stand as, and a reader asking
     * what a use of the name runs is asking about this value and not about where it ends.
     */
    public List<Denotation> boundTo(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        if (!(Core.withoutStanding(e) instanceof Core.Read read)) {
            return List.of();
        }
        return switch (ValueStanding.named(read, this,
                new Followed(symbols, newtypes, new HashSet<>()))) {
            case null -> List.of();
            case ValueStanding.Named.One<InputReads, Followed>(var one) ->
                    List.of(new Denotation(one.value(), one.at()));
            case ValueStanding.Named.OneOf<InputReads, Followed>(var members) ->
                    members.stream().map(one -> new Denotation(one.value(), one.at())).toList();
        };
    }

    /**
     * What {@code e} stands as here, as a value a reader may take apart: each part it finds is
     * followed where {@code e} was written ({@link ValueStanding.Standing#part}).
     */
    public ValueStanding.Standing<InputReads, ?> standingValue(Core e, Symbols symbols,
                                                              DeclarationNewtypes newtypes) {
        return ValueStanding.one(e, this, new Followed(symbols, newtypes, new HashSet<>()));
    }

    /**
     * {@code from} followed through the steps that have one successor, as far as they go
     * ({@link ValueStanding}).
     *
     * <p>A normal form and never a failure: what comes back where nothing applies is what went in,
     * which a caller reads rather than treating as an absence.
     *
     * <p><b>Which names are followed is {@link #meaningOf}'s answer and is not read off the bindings
     * here.</b> A name is a position, or one of several values, or an element, before it is what it
     * was bound to, and there is no way to read a binding's value here without that order having
     * been applied: the environment answers what a name is ({@link BindingRole}) and hands out
     * nothing to put in a different order. What would have told a second order apart is a binding
     * that both holds a value and is what an operation handed an element on, which is the shape
     * joining two walks leaves.
     *
     * <p>No plurality is followed into. A name that is one of several values stands as the name,
     * which is what a reader asking for one value is owed.
     */
    static Denotation standing(Denotation from, Symbols symbols,
                               DeclarationNewtypes newtypes, Set<BindingId> met) {
        ValueStanding.Standing<InputReads, Followed> stands =
                ValueStanding.one(from.value(), from.at(), new Followed(symbols, newtypes, met));
        return new Denotation(stands.value(), stands.at());
    }

    /**
     * What this reading answers about names, for the walk that follows them.
     *
     * <p>By the bindings met, which is what makes a walk stop: each tells itself from every other,
     * so a name that came round to itself is one already answered for. Shared with
     * {@link #meaningOf}, which follows a container to its elements by this same walk, so the two
     * stop at the same names.
     */
    private record Followed(Symbols symbols, DeclarationNewtypes newtypes, Set<BindingId> met)
            implements ValueStanding.Names<InputReads, Followed> {

        private Followed {
            Objects.requireNonNull(newtypes, "a name is followed knowing what each name wraps");
        }

        @Override
        public ValueStanding.ReadThrough<InputReads> readThrough(Core.Read read, InputReads at) {
            if (!met.add(read.binding())
                    || !(at.meaningOf(read, symbols, newtypes, met)
                            instanceof ReadMeaning.Through through)) {
                return null;
            }
            return new ValueStanding.ReadThrough<>(through.denotes().value(),
                    through.denotes().at());
        }

        @Override
        public List<ValueStanding.ReadThrough<InputReads>> alternativesOf(Core.Read read,
                                                                          InputReads at) {
            return null;
        }

        @Override
        public InputReads inside(Core.LetIn li, InputReads at) {
            return at.and(li.binder(), li.value());
        }

        // A value this reading takes as another is that value: a choice the answer of the arm it
        // is on, a call the body it entered.
        @Override
        public ValueStanding.ReadThrough<InputReads> taken(Core node, InputReads at) {
            Denotation as = at.taken(node);
            return as == null ? null : new ValueStanding.ReadThrough<>(as.value(), as.at());
        }

        @Override
        public Followed oneAtATime() {
            return this;
        }
    }

    /**
     * The string {@code e} stands for here, or null where nothing here says it is one.
     *
     * <p>What a name stands for is this reading's question and is answered here rather than by
     * whoever wants the string. A rule written {@code String.startsWith(prefix, code)} under
     * {@code let prefix = "JP"} states the same thing as one written with the string in it, and a
     * reader that took the argument as it was written would have the two mean different things —
     * not because the compiler cannot work the second out, but because the reader did not take the
     * answer this already has.
     *
     * <p>Folded as the discharge of a rule folds the same argument ({@link #folded}): through the
     * names, the fields and elements taken off what was written, and the operators over the texts
     * those reach. An expression that stands for something computed from an input is a string
     * nothing here works out, and it is null the way anything else this cannot answer is.
     */
    public String writtenStringOf(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return folded(e, symbols, newtypes).orElse(null) instanceof String written ? written : null;
    }

    /**
     * What {@code e} comes to at compile time read here ({@link FoldedValue}), or empty where it is
     * not a constant: names followed as this reading follows them, and the operators over what they
     * reach folded as the discharge of a rule folds them.
     */
    public Optional<Object> folded(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return FoldedValue.of(e, this, new Followed(symbols, newtypes, new HashSet<>()), symbols);
    }

    /** Where an element handed to {@code binding} stands ({@link InputPath#elementAt}), at a
     *  position and never at a narrowing of one to several cases ({@link PathResolution#heldAt}). */
    public PathResolution elementAt(BindingId binding, DeclarationNewtypes newtypes) {
        return InputPath.elementAt(binding, names, newtypes, this).heldAt();
    }

    /** Where the elements {@code e} holds stand, where it holds every occurrence of that position
     *  and each as often ({@link InputPath#everyElementOf}). */
    public PathResolution everyElementOf(Core e, DeclarationNewtypes newtypes) {
        return InputPath.everyElementOf(e, names, newtypes, this);
    }

    /**
     * The container whose every element {@code e} holds, each as often, though {@code e} may be no
     * place a row writes — a list in another order is one — or null where it holds no such
     * container's.
     *
     * <p>Only a container that stands inside no other. The elements of what a flattening made
     * stand inside two, and a list inside the elements of another holds some of the occurrences of
     * its path: no statement about the elements of one container says what those do.
     */
    public TermPath containerWhoseEveryElementIsIn(Core e, DeclarationNewtypes newtypes) {
        if (!(everyElementOf(e, newtypes) instanceof PathResolution.At(TermPath elements))
                || !(elements.steps().getLast() instanceof TermPath.Step.Element)) {
            return null;
        }
        List<TermPath> holding = elements.containersHoldingIt();
        return holding.size() == 1 ? holding.getFirst() : null;
    }

    /** The same, of the elements handed to {@code binding} ({@link InputPath#everyElementAt}). */
    public PathResolution everyElementAt(BindingId binding, DeclarationNewtypes newtypes) {
        return InputPath.everyElementAt(binding, names, newtypes, this);
    }

    /** The same, where the elements handed to {@code binding} are also handed in {@code direction}
     *  ({@link InputPath#inTheOrderAt}). */
    public PathResolution inTheOrderAt(BindingId binding, TraversalDirection direction,
                                       DeclarationNewtypes newtypes) {
        return InputPath.inTheOrderAt(binding, direction, names, newtypes, this);
    }

    /** The same, of the elements {@code e} holds ({@link InputPath#inTheOrderOf}). */
    public PathResolution inTheOrderOf(Core e, TraversalDirection direction,
                                       DeclarationNewtypes newtypes) {
        return InputPath.inTheOrderOf(e, direction, names, newtypes, this);
    }

    /** Where {@code e}'s value came from. Not where it is: a value made from a position is not that
     *  position ({@link InputPath#cameFrom}). */
    public PathResolution cameFrom(Core e, DeclarationNewtypes newtypes) {
        return InputPath.cameFrom(e, names, newtypes, this).heldAt();
    }

    /**
     * Two readings are one where they hold the same facts and stand under the same arms.
     *
     * <p>A value and not an identity, because it travels inside one: a name stands for a value in
     * the environment its binding was made in, and the two are carried together ({@link Denotation}).
     * Told apart by which copy a caller had, one value read in two equal environments would be two
     * values wherever a reader compares what it was answered.
     */
    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof InputReads that && names.equals(that.names)
                        && alternatives.equals(that.alternatives)
                        && declared.equals(that.declared)
                        && dependencies.equals(that.dependencies)
                        && applied.equals(that.applied));
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0) {
            h = Objects.hash(names, alternatives, declared, dependencies, applied);
            hash = h;
        }
        return h;
    }

    @Override
    public String toString() {
        return "InputReads[names=" + names + ", alternatives=" + alternatives + ", declared="
                + declared + "]";
    }
}
