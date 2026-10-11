package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.UnaryOperator;

/**
 * The applications of the closures a place in a body stands inside, where each is handed one of
 * the values a container was written with: in the order a run makes them, each read in the names
 * that application hands over and with what has to hold for a run to make it.
 *
 * <p>Carried down a walk beside the names it reads, and moved by the same steps. A comparison in a
 * closure is one construct the author wrote, met on every application, so what it states is read
 * once per application at the comparison — under the names that application binds on the way
 * there, which are the walk's own names with the value it was handed in place of the parameter.
 *
 * <p>What has to hold for an application to be made is said before anything is made of what the
 * comparison states on it ({@link WhereAnApplicationIsMade}): it is a fact about the order and the
 * operation, and two applications stating one thing are two applications.
 */
sealed interface ClosureApplications {

    /** Inside no closure handed values written out. */
    ClosureApplications OUTSIDE = new Outside();

    /** Inside no closure handed values written out. */
    record Outside() implements ClosureApplications {}

    /**
     * Inside closures whose applications are said, in the order a run makes them.
     *
     * @param each every application, nested ones taken together with the ones around them
     */
    record Each(List<Application> each) implements ClosureApplications {

        public Each {
            each = List.copyOf(each);
            if (each.isEmpty()) {
                throw new IllegalArgumentException("a closure applied is applied some times");
            }
        }
    }

    /**
     * Inside a closure whose applications are not said — more of them than are read, or values
     * handed that this reading cannot name — so what is in it is read once, as it stands.
     */
    record NotSaid() implements ClosureApplications {}

    /**
     * Inside a closure no run applies: it is handed the elements of a container that holds none on
     * any row, inside every application around it that is made. Nothing in it is reached, so
     * nothing in it is read — and closures inside it are applied by nothing either.
     *
     * <p>The opposite of {@link NotSaid}, which reads what is in a closure once because some run
     * may apply it to something nobody wrote down.
     */
    record None() implements ClosureApplications {}

    /**
     * One application.
     *
     * @param reads             the names in force at it, with the value it was handed in place of
     *                          the parameter
     * @param reached           what has to hold for a run to make it
     * @param carriedIntoTheFirst what each walk from a seed this is inside carries into its first
     *                          step — its seed — by the binding the step takes it on
     *                          ({@link #taking})
     */
    record Application(InputReads reads, Proposition reached,
                       Map<BindingId, Denotation> carriedIntoTheFirst) {

        public Application {
            Objects.requireNonNull(reads, "an application is read in some names");
            Objects.requireNonNull(reached, "and is made under something");
            carriedIntoTheFirst = Collections.unmodifiableMap(
                    new LinkedHashMap<>(carriedIntoTheFirst));
        }
    }

    /**
     * The applications inside {@code block}, entered by {@code step} from where it stands, which
     * is read in {@code reads} by a walk that is inside these.
     */
    default ClosureApplications into(Core.Block block, ScopeStep step, InputReads reads,
                                     InputReading read) {
        return switch (this) {
            case Outside _ -> applied(block, step,
                    List.of(new Application(reads, WhereAnApplicationIsMade.nothingAsked(),
                            Map.of())),
                    read, true);
            case Each(var outer) -> applied(block, step, outer, read, false);
            case NotSaid _, None _ -> this;
        };
    }

    /**
     * The applications of {@code block} made inside each of {@code outer} — and where the block is
     * handed nothing written out, each of {@code outer} past the step into it, or nothing at all
     * where {@code outer} stands for being inside no closure. Inside an application around it where
     * the block is applied to nothing, it adds no application; where that is so inside every one,
     * no run applies it ({@link None}).
     */
    private static ClosureApplications applied(Core.Block block, ScopeStep step,
                                               List<Application> outer, InputReading read,
                                               boolean outside) {
        Symbols symbols = read.symbols();
        DeclarationNewtypes newtypes = read.newtypes();
        List<Application> out = new ArrayList<>();
        boolean handed = false;
        boolean asked = false;
        for (Application around : outer) {
            switch (Pullback.applicationsOf(block, around.reads(), read)) {
                case InputReads.Applications.NoneMade _ -> handed = true;
                case InputReads.Applications.Each(var each, var how) -> {
                    handed = true;
                    List<Proposition> answers = how == HowAClosureIsApplied.TO_EVERY_ELEMENT ? null
                            : each.stream().map(one -> Pullback.ofATruth(block.body(), one.reads(),
                                    read, Optional.empty()).proposition()).toList();
                    List<List<Proposition>> keptBy = each.stream()
                            .map(one -> keptBy(one.keptWhere(), read)).toList();
                    List<Proposition> reached = WhereAnApplicationIsMade.reached(answers, keptBy,
                            how, around.reached());
                    for (int at = 0; at < each.size(); at++) {
                        out.add(new Application(each.get(at).reads(), reached.get(at),
                                around.carriedIntoTheFirst()));
                    }
                }
                case InputReads.Applications.NoneHanded _ -> {
                    List<DecisionSubject> appliedOver =
                            positionsAppliedOver(block, around.reads(), read).stream()
                                    .<DecisionSubject>map(DecisionSubject.AnInput::new).toList();
                    asked |= !appliedOver.isEmpty();
                    out.add(new Application(around.reads().entering(step, symbols, newtypes),
                            appliedOver.isEmpty() ? around.reached()
                                    : WhereAnApplicationIsMade.whereOneOfTheContainersHoldsSomething(
                                            around.reached(), appliedOver),
                            around.carriedIntoTheFirst()));
                }
                case InputReads.Applications.Unsaid _,
                     InputReads.Applications.MoreThanAreRead _ -> {
                    return new NotSaid();
                }
            }
        }
        if (out.isEmpty()) {
            return new None();
        }
        return handed || asked || !outside ? new Each(out) : OUTSIDE;
    }

    /**
     * What each truth an element was kept by states, read where it was decided, and denied where it
     * was kept by the truth failing. A truth this cannot read is said as one it did not read, and
     * not as one that holds: an application it decides is one a run may not make.
     */
    private static List<Proposition> keptBy(List<ReadMeaning.Occurrence.Kept> keptWhere,
                                            InputReading read) {
        return keptWhere.stream().map(kept -> {
            Proposition stated = Pullback.ofATruth(kept.truth().value(), kept.truth().at(), read,
                    Optional.empty()).proposition();
            return kept.holds() ? stated : stated.denied();
        }).toList();
    }

    /**
     * The positions of the input the containers {@code block} is applied over stand at, or none
     * where there are none or one of them stands at no position.
     *
     * <p>Every one or nothing: a run may be inside the closure by the operation over the container
     * that stands at no position with every other empty, so saying one of the rest holds something
     * would be saying more than is known.
     */
    private static List<TermPath> positionsAppliedOver(Core.Block block, InputReads reads,
                                                       InputReading read) {
        List<TermPath> out = new ArrayList<>();
        for (Denotation container : reads.containersAppliedOver(block)) {
            Optional<TermPath> at = Pullback.positionHoldingWhatItHolds(container, read);
            if (at.isEmpty()) {
                return List.of();
            }
            out.add(at.get());
        }
        return List.copyOf(out);
    }

    /**
     * Whether what holds on the way to a place inside these is said of each application. Where it
     * is, a condition met inside the closure goes onto what each application is reached under,
     * read in that application's names, and not onto the way every application shares — read
     * there, it would be read with the parameter standing for any of the values at once.
     */
    default boolean saysWhatStandsInIt() {
        return this instanceof Each || this instanceof None;
    }

    /**
     * The same applications past {@code condition} coming out {@code holding} on each of them.
     *
     * <p>A condition on what a walk carried says nothing a row can be asked for, but on the walk's
     * first step what it carried is its seed. Where the condition, read with each walk around the
     * application carrying its seed, comes out {@code holding} whatever the row is, the first step
     * gets past it, so a run making the application at all makes one past it, and it is left
     * standing under what it was reached under. Anything less settled than that is no such
     * account: a later step past it would be a step the seed says nothing of.
     */
    default ClosureApplications taking(Core condition, boolean holding, InputReading read) {
        return switch (this) {
            case Each(var each) -> new Each(each.stream().map(one -> {
                Proposition stated = Pullback.ofATruth(condition, one.reads(), read,
                        Optional.empty()).proposition();
                Proposition past = holding ? stated : stated.denied();
                return Proposition.leavesSomethingUnread(past)
                        && pastOnTheFirstStep(condition, holding, one, read) ? one
                        : new Application(one.reads(), WhereAnApplicationIsMade.past(
                                one.reached(), past), one.carriedIntoTheFirst());
            }).toList());
            case Outside _, NotSaid _, None _ -> this;
        };
    }

    /** Whether {@code condition} comes out {@code holding} on {@code one} whatever the row is,
     *  read with every walk around it carrying its seed. */
    private static boolean pastOnTheFirstStep(Core condition, boolean holding, Application one,
                                              InputReading read) {
        if (one.carriedIntoTheFirst().isEmpty()) {
            return false;
        }
        InputReads first = one.reads();
        for (Map.Entry<BindingId, Denotation> seed : one.carriedIntoTheFirst().entrySet()) {
            first = first.handing(seed.getKey(), seed.getValue(), read.newtypes());
        }
        return Pullback.ofATruth(condition, first, read, Optional.empty()).proposition()
                instanceof Proposition.Always(boolean holds) && holds == holding;
    }

    /**
     * The same applications, inside the step of a walk from a seed that takes what it carries on
     * {@code accumulator} and starts from {@code seed}.
     */
    default ClosureApplications carryingIntoTheFirst(Core.Binder accumulator, Denotation seed) {
        if (!(this instanceof Each(var each))) {
            return this;
        }
        return new Each(each.stream().map(one -> {
            Map<BindingId, Denotation> carried = new LinkedHashMap<>(one.carriedIntoTheFirst());
            carried.put(accumulator.binding(), seed);
            return new Application(one.reads(), one.reached(), carried);
        }).toList());
    }

    /** The same applications past {@code step}. */
    default ClosureApplications entering(ScopeStep step, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        return step instanceof ScopeStep.Chosen(Choice.Decides decidedBy)
                ? choosing(decidedBy, symbols, newtypes)
                : moved(reads -> reads.entering(step, symbols, newtypes));
    }

    /** The same applications with {@code binder} standing for {@code value}. */
    default ClosureApplications and(Core.Binder binder, Core value) {
        return moved(reads -> reads.and(binder, value));
    }

    /**
     * The applications that enter the arm {@code decidedBy} decides, inside it.
     *
     * <p>An application handed a value of a case the arm does not take never enters it, so it is
     * left out rather than read in an arm it does not reach. Where none enters, no run reaches
     * what is in the arm ({@link None}).
     */
    default ClosureApplications choosing(Choice.Decides decidedBy, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        if (!(this instanceof Each(var each))) {
            return this;
        }
        List<Application> entering = each.stream()
                .filter(one -> mayEnter(one, decidedBy, symbols, newtypes))
                .map(one -> new Application(one.reads().choosing(decidedBy, symbols, newtypes),
                        one.reached(), one.carriedIntoTheFirst()))
                .toList();
        return entering.isEmpty() ? new None() : new Each(entering);
    }

    /**
     * Whether {@code one} may enter the arm {@code decidedBy} decides: everywhere but an arm of a
     * case its value is known not to take. Every other way of deciding an arm turns on what the row
     * holds, and an application is read in it as one the row may take.
     */
    private static boolean mayEnter(Application one, Choice.Decides decidedBy, Symbols symbols,
                                    DeclarationNewtypes newtypes) {
        return switch (decidedBy) {
            case Choice.Decides.ACase arm -> !one.reads()
                    .whetherEveryRowTakes(arm.arm(), arm.scrutinee(), symbols, newtypes)
                    .equals(Optional.of(false));
            case Choice.Decides.ACondition _ -> true;
            case Choice.Decides.ItWasBuilt _ -> true;
            case Choice.Decides.ItDeparted _ -> true;
            case Choice.Decides.ByArgumentRelations _ -> true;
        };
    }

    private ClosureApplications moved(UnaryOperator<InputReads> step) {
        return switch (this) {
            case Each(var each) -> new Each(each.stream()
                    .map(one -> new Application(step.apply(one.reads()), one.reached(),
                            one.carriedIntoTheFirst()))
                    .toList());
            case Outside _, NotSaid _, None _ -> this;
        };
    }
}
