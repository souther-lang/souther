package souther.compiler.inputs;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.CaseSelector;
import souther.compiler.types.TypeSymbol;

import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Optional;
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
 */
public final class InputReads {

    private final BindingEnvironment names;
    private final Map<BindingId, java.util.List<Denotation>> alternatives;
    private final DeclaredInput declared;

    private InputReads(BindingEnvironment names,
                       Map<BindingId, java.util.List<Denotation>> alternatives,
                       DeclaredInput declared) {
        this.names = names;
        this.alternatives = Map.copyOf(alternatives);
        this.declared = declared;
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
     */
    public static InputReads ofParameters(Map<BindingId, String> parameters,
                                          DeclaredInput declared, ElementBindings elements) {
        return new InputReads(new BindingEnvironment(BindingEnvironment.rooted(parameters),
                Map.of(), elements, false), Map.of(), declared);
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
     */
    public static InputReads ofParametersWhereCallsStand(
            Map<BindingId, String> parameters, DeclaredInput declared, ElementBindings elements) {
        return new InputReads(new BindingEnvironment(BindingEnvironment.rooted(parameters),
                Map.of(), elements, true), Map.of(), declared);
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
                ElementBindings.NONE, true), Map.of(), declared);
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
                ElementBindings.NONE, true), Map.of(), declared);
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
        return new InputReads(new BindingEnvironment(roots, bound, elements, false), Map.of(),
                DeclaredInput.NONE);
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
        if (arm.binder() == null || arm.binder().binding() == null) {
            return this;
        }
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
            case PathResolution.MayStandAt _ -> null;
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
                declared);
    }

    /**
     * The same, where what the arm binds is one of the values the scrutinee's set holds.
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
        if (one == null) {
            return denotingWhatWasMatched(scrutinee, arm, symbols, newtypes);
        }
        for (CaseSelector selector : arm.pattern().selectors()) {
            if (!(selector.refinement() instanceof souther.compiler.types.Refinement.Direct)) {
                return this;
            }
        }
        java.util.List<Denotation> left = new java.util.ArrayList<>();
        for (Denotation each : one.alternatives()) {
            Optional<TypeSymbol> written = WrittenCase.of(each.value());
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
        Map<BindingId, java.util.List<Denotation>> wider = new LinkedHashMap<>(alternatives);
        wider.put(arm.binder().binding(), left);
        return new InputReads(names, wider, declared);
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
        Set<TypeSymbol> out = new LinkedHashSet<>();
        for (Denotation each : many.alternatives()) {
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
            case ScopeStep.Block _ -> this;
        };
    }

    /** The same, inside what {@code binder} binds. */
    public InputReads and(Core.Binder binder, Core value) {
        BindingEnvironment inside = names.inside(binder, value);
        return inside == names ? this : new InputReads(inside, alternatives, declared);
    }

    /**
     * Where {@code e} stands, read here ({@link PathResolution}): a position, and never a narrowing
     * of one to several cases ({@link PathResolution#heldAt}).
     */
    public PathResolution pathOf(Core e, DeclarationNewtypes newtypes) {
        return InputPath.of(e, names, newtypes).heldAt();
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
        return InputPath.of(e, names, newtypes);
    }

    /** Where in the element handed to {@code binding} the value a walk answered stands, or null
     *  where the walk answered no place of it ({@link ElementProjection}). */
    ElementProjection projectionAt(BindingId binding) {
        return names.projectionAt(binding);
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
        return writtenOut(new Denotation(e, this), symbols, newtypes, new HashSet<>());
    }

    private static boolean writtenOut(Denotation from, Symbols symbols,
                                      DeclarationNewtypes newtypes, Set<BindingId> met) {
        Denotation at = standing(from, symbols, newtypes, met);
        InputReads reads = at.at();
        return switch (Core.withoutStanding(at.value())) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _, Core.OptionNone _ -> true;
            case Core.Read name -> reads.meaningOf(name, symbols, newtypes, new HashSet<>(met))
                    instanceof ReadMeaning.OneOf one
                    && one.alternatives().stream()
                            .allMatch(each -> writtenOut(each, symbols, newtypes,
                                    new HashSet<>(met)));
            case Core.Neg negated -> writtenOut(new Denotation(negated.operand(), reads),
                    symbols, newtypes, new HashSet<>(met));
            case Core.OptionSome some -> writtenOut(new Denotation(some.value(), reads),
                    symbols, newtypes, new HashSet<>(met));
            case Core.ListLit list -> list.elements().stream()
                    .allMatch(each -> writtenOut(new Denotation(each, reads), symbols, newtypes,
                            new HashSet<>(met)));
            case Core.Tuple tuple -> tuple.elements().stream()
                    .allMatch(each -> writtenOut(new Denotation(each, reads), symbols, newtypes,
                            new HashSet<>(met)));
            case Core.Construct made -> made.values().stream()
                    .allMatch(each -> writtenOut(new Denotation(each.value(), reads), symbols,
                            newtypes, new HashSet<>(met)));
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
            case PathResolution.MayStandAt _ -> { }
        }
        java.util.List<Denotation> narrowed = alternatives.get(read.binding());
        if (narrowed != null) {
            return new ReadMeaning.OneOf(narrowed);
        }
        return switch (names.roleOf(read.binding())) {
            case BindingRole.Element(var container) -> {
                java.util.List<Denotation> written =
                        writtenElementsOf(new Denotation(container, this), symbols, newtypes, met);
                yield written == null ? new ReadMeaning.Element() : new ReadMeaning.OneOf(written);
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
                    : new ReadMeaning.Through(new Denotation(value, this));
            case BindingRole.Unknown _ -> new ReadMeaning.Unknown();
            // A parameter is the position it is the name of. The walk above reaches it by the same
            // fact, so nothing gets here — and what would be said if anything did is what is said
            // there, rather than a failure invented to fill the arm.
            case BindingRole.Root(var at) -> new ReadMeaning.Position(at);
        };
    }

    /**
     * The elements {@code container} was written with, or null where it was not written out.
     *
     * <p>What makes this an answer about every element and not about some of them is that the
     * container is followed only through steps with one successor — a name this environment bound,
     * and the body of a binding — until a list written in the source is standing there. An operation
     * that builds a container answers elements this walk cannot enumerate, and the walk stops rather
     * than reading what went in: {@code List.append(xs, ys)} holds the elements of both, and a
     * reading that took either would have written out a set missing the other half.
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
    private static java.util.List<Denotation> writtenElementsOf(Denotation container,
                                                                Symbols symbols,
                                                                DeclarationNewtypes newtypes,
                                                                Set<BindingId> met) {
        Denotation standing = standing(container, symbols, newtypes, met);
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
     * {@code from} followed through the steps that have one successor, as far as they go.
     *
     * <p>A name standing for one value and the body of a binding, and nothing else. A normal form
     * and never a failure: what comes back where nothing applies is what went in, which a caller
     * reads rather than treating as an absence.
     *
     * <p><b>Which names those are is {@link #meaningOf}'s answer and is not read off the bindings
     * here.</b> A name is a position, or one of several values, or an element, before it is what it
     * was bound to, and there is no way to read a binding's value here without that order having
     * been applied: the environment answers what a name is ({@link BindingRole}) and hands out
     * nothing to put in a different order. What would have told a second order apart is a binding
     * that both holds a value and is what an operation handed an element on, which is the shape
     * joining two walks leaves.
     *
     * <p>By the bindings met, which is what makes it stop. Each tells itself from every other, so a
     * name that came round to itself is one already answered for.
     */
    private static Denotation standing(Denotation from, Symbols symbols,
                                       DeclarationNewtypes newtypes, Set<BindingId> met) {
        Denotation at = from;
        while (true) {
            switch (at.value()) {
                case Core.Read name -> {
                    if (!met.add(name.binding())
                            || !(at.at().meaningOf(name, symbols, newtypes, met)
                                    instanceof ReadMeaning.Through through)) {
                        return at;
                    }
                    at = through.denotes();
                }
                case Core.LetIn let ->
                        at = new Denotation(let.body(), at.at().and(let.binder(), let.value()));
                // What a value is does not turn on the type it stands as.
                case Core.Widen w -> at = new Denotation(w.value(), at.at());
                default -> {
                    return at;
                }
            }
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
     * <p>Through the names and no further ({@link #standing}). What comes back is the value the
     * expression stands for once the names have been followed, and a string is what it is where
     * that value is one written down. An expression that stands for something computed is a string
     * nothing here works out, and it is null the way anything else this cannot answer is —
     * arithmetic over the values is not a question a naming answers.
     */
    public String writtenStringOf(Core e, Symbols symbols, DeclarationNewtypes newtypes) {
        return Core.withoutStanding(standing(new Denotation(e, this), symbols, newtypes,
                new HashSet<>()).value()) instanceof Core.Str written ? written.value() : null;
    }

    /** Where an element handed to {@code binding} stands ({@link InputPath#elementAt}), at a
     *  position and never at a narrowing of one to several cases ({@link PathResolution#heldAt}). */
    public PathResolution elementAt(BindingId binding, DeclarationNewtypes newtypes) {
        return InputPath.elementAt(binding, names, newtypes).heldAt();
    }

    /** Where {@code e}'s value came from. Not where it is: a value made from a position is not that
     *  position ({@link InputPath#cameFrom}). */
    public PathResolution cameFrom(Core e, DeclarationNewtypes newtypes) {
        return InputPath.cameFrom(e, names, newtypes).heldAt();
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
                        && declared.equals(that.declared));
    }

    @Override
    public int hashCode() {
        return (names.hashCode() * 31 + alternatives.hashCode()) * 31 + declared.hashCode();
    }

    @Override
    public String toString() {
        return "InputReads[names=" + names + ", alternatives=" + alternatives + ", declared="
                + declared + "]";
    }
}
