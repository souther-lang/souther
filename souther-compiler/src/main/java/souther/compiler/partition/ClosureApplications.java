package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.check.QuotientByAValue;
import souther.compiler.check.WhatARunMayEndFor;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.semantics.HowAClosureIsApplied;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.function.Function;
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

    /** Inside no closure at all. */
    ClosureApplications OUTSIDE = new Outside(ElementsMetOn.EVERY);

    /**
     * Inside no closure handed values written out.
     *
     * @param metOn which elements of the input a run makes what stands here on, where it stands
     *              inside closures over the input's containers: nothing about each application is
     *              said here, and which elements a run gets to still is
     */
    record Outside(ElementsMetOn metOn) implements ClosureApplications {

        public Outside {
            Objects.requireNonNull(metOn, "what stands here is made on some elements");
        }
    }

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
     *
     * <p>And which elements of the input a run makes what is in it on is not said either, for
     * the same reason: what the closures around it were known of is kept, and within any element
     * of theirs whether this one is made is what is not said.
     *
     * @param metOn which elements what stands here is made on: the closures around it, and nothing
     *              said of any element within them
     */
    record NotSaid(ElementsMetOn metOn) implements ClosureApplications {

        public NotSaid {
            Objects.requireNonNull(metOn, "what stands here is made on some elements, or unsaid ones");
        }
    }

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
     * @param metOn             which elements of the containers of the input it is made on, where
     *                          it is one application standing for every element of one: an
     *                          operation that stops at an answer makes it on an element only where
     *                          none before it stopped the operation
     */
    record Application(InputReads reads, Proposition reached,
                       Map<BindingId, Denotation> carriedIntoTheFirst, ElementsMetOn metOn) {

        public Application {
            Objects.requireNonNull(reads, "an application is read in some names");
            Objects.requireNonNull(reached, "and is made under something");
            Objects.requireNonNull(metOn, "and on some elements");
            carriedIntoTheFirst = Collections.unmodifiableMap(
                    new LinkedHashMap<>(carriedIntoTheFirst));
        }
    }

    /**
     * Which elements of the input a comparison standing inside these is made on.
     *
     * <p>One answer however many applications there are, where they agree; where they say
     * different things — closures over values written out, around one over the input — which of
     * them a row's element was met through is not said. Never every element for want of knowing:
     * a closure whose applications are not said is made on elements nothing here says.
     *
     * <p>Inside a closure no run applies, nothing is read, so nothing asks; it is every element
     * only in the sense that no reading of it is ever put to a row.
     */
    default ElementsMetOn elementsMetOn() {
        return switch (this) {
            case Outside(var metOn) -> metOn;
            case NotSaid(var metOn) -> metOn;
            case None _ -> ElementsMetOn.EVERY;
            case Each(var each) -> {
                ElementsMetOn first = each.getFirst().metOn();
                yield each.stream().allMatch(one -> one.metOn().equals(first)) ? first
                        : ElementsMetOn.EVERY.notSaidAnywhere(
                                ReadingGap.REACH_IS_NO_VALUE_OF_THE_ROW);
            }
        };
    }

    /**
     * The applications inside {@code block}, entered by {@code step} from where it stands, which
     * is read in {@code reads} by a walk that is inside these.
     */
    default ClosureApplications into(Core.Block block, ScopeStep step, InputReads reads,
                                     InputReading read) {
        return switch (this) {
            case Outside(var metOn) -> applied(block, step,
                    List.of(new Application(reads, WhereAnApplicationIsMade.nothingAsked(),
                            Map.of(), metOn)),
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
        // Whether what the block's body states may answer nothing on some rows: one question of
        // the block, whichever application around it is asking, and asked only of one applied to
        // every value.
        Boolean mayAnswerNothing = null;
        for (Application around : outer) {
            switch (Pullback.applicationsOf(block, around.reads(), read)) {
                case InputReads.Applications.NoneMade _ -> handed = true;
                case InputReads.Applications.Each(var each, var how) -> {
                    handed = true;
                    // Applied to every value, an application is made past the ones before it only
                    // where each of them answered, as a reading reads where a statement answers;
                    // what a body that is no truth answers is no statement read here, so which of
                    // those a run gets past is not said.
                    boolean toEvery = how == HowAClosureIsApplied.TO_EVERY_ELEMENT;
                    if (toEvery && mayAnswerNothing == null) {
                        mayAnswerNothing = WhatARunMayEndFor.of(block.body())
                                .mayEndFor(QuotientByAValue.WHERE_IT_ANSWERS_NOTHING);
                    }
                    if (toEvery && mayAnswerNothing && !Type.BOOL.equals(block.body().type())) {
                        return new NotSaid(around.metOn().notSaidAnywhere(
                                new ReadingGap.ReachNotRead(
                                        ReadingGap.ReachNotRead.Why.A_PART_NOT_READ)));
                    }
                    List<Proposition> answers = toEvery && !mayAnswerNothing ? null
                            : each.stream().map(one -> WhatConditionsState.of(read)
                                    .truth(block.body(), one.reads(), read).proposition()).toList();
                    List<List<Proposition>> keptBy = each.stream()
                            .map(one -> keptBy(one.keptWhere(), read)).toList();
                    List<Proposition> reached = WhereAnApplicationIsMade.reached(answers, keptBy,
                            how, around.reached());
                    for (int at = 0; at < each.size(); at++) {
                        out.add(new Application(each.get(at).reads(), reached.get(at),
                                around.carriedIntoTheFirst(), around.metOn()));
                    }
                }
                case InputReads.Applications.NoneHanded _ -> {
                    List<InputReads.AppliedOver> appliedOver =
                            around.reads().containersAppliedOver(block);
                    List<Denotation> containers = appliedOver.stream()
                            .map(InputReads.AppliedOver::container).toList();
                    Optional<WhereAClosureIsApplied> where =
                            WhereAClosureIsApplied.of(appliedOver, read);
                    asked |= where.isPresent();
                    InputReads entered = around.reads().entering(step, symbols, newtypes);
                    out.add(new Application(entered,
                            where.map(some -> WhereAnApplicationIsMade.past(around.reached(),
                                    some.holdingSomething())).orElse(around.reached()),
                            around.carriedIntoTheFirst(),
                            metOn(block, containers, around, entered, read)));
                }
                case InputReads.Applications.Unsaid _ -> {
                    return new NotSaid(around.metOn().notSaidAnywhere(new ReadingGap.ReachNotRead(
                            ReadingGap.ReachNotRead.Why.A_PART_NOT_READ)));
                }
                case InputReads.Applications.MoreThanAreRead _ -> {
                    return new NotSaid(around.metOn().notSaidAnywhere(new ReadingGap.ReachNotRead(
                            ReadingGap.ReachNotRead.Why.MORE_READINGS_THAN_ARE_MADE)));
                }
                case InputReads.Applications.PastWhatIsWrittenOut _ -> {
                    return new NotSaid(around.metOn().notSaidAnywhere(new ReadingGap.ReachNotRead(
                            ReadingGap.ReachNotRead.Why.MORE_ELEMENTS_THAN_ARE_WRITTEN_OUT)));
                }
            }
        }
        if (out.isEmpty()) {
            return new None();
        }
        // Outside every closure handed values written out, there is one application, and what is
        // kept of it is which elements it is made on.
        return handed || asked || !outside ? new Each(out) : new Outside(out.getFirst().metOn());
    }

    /**
     * Which elements the application of {@code block} that stands for every element of what it is
     * handed — {@code containers} — is made on: those {@code around} is made on, and where the operation stops at an
     * answer, the elements no element before stopped it at — what the closure answers on one,
     * read in the names {@code entered} it with.
     *
     * <p>Only over a container that is itself a position of the input, whose elements are the
     * row's in the row's order. Anything made of one — a filter, a reversal, a map filed from a
     * list — is applied over in an order and over elements the row does not write, so which element
     * stopped the operation there is said not to be said. An operation applying its closure to
     * every element adds nothing. One applying it to an element it picks out, or to some, makes it
     * on elements nothing here reads, and so does one handing a parameter the elements of several
     * containers each applied its own way: said not to be said of those containers, and never
     * every element for want of knowing. A closure handed no element at all is made on the
     * elements {@code around} is.
     */
    private static ElementsMetOn metOn(Core.Block block, List<Denotation> containers,
                                       Application around, InputReads entered,
                                       InputReading read) {
        List<HowAClosureIsApplied> applied = around.reads().howItIsApplied(block);
        if (applied.stream().allMatch(HowAClosureIsApplied.TO_EVERY_ELEMENT::equals)) {
            return around.metOn();
        }
        if (applied.size() > 1) {
            return notSaid(around.metOn(), containers, read,
                    new ReadingGap.ReachNotRead(ReadingGap.ReachNotRead.Why.A_PART_NOT_READ));
        }
        HowAClosureIsApplied how = applied.getFirst();
        return switch (how) {
            case TO_EVERY_ELEMENT -> around.metOn();
            case AT_MOST_ONE, TO_SOME -> notSaid(around.metOn(), containers, read,
                    new ReadingGap.ReachNotRead(ReadingGap.ReachNotRead.Why.A_PART_NOT_READ));
            case UNTIL_ONE_HOLDS, UNTIL_ONE_FAILS -> {
                if (containers.size() != 1 || !(containers.getFirst().at().pathOf(
                        containers.getFirst().value(), read.newtypes())
                        instanceof PathResolution.At(TermPath container))) {
                    yield notSaid(around.metOn(), containers, read,
                            ReadingGap.REACH_IS_NO_VALUE_OF_THE_ROW);
                }
                WhatConditionsState conditions = WhatConditionsState.of(read);
                Proposition answered = conditions.truth(block.body(), entered, read)
                        .proposition();
                yield around.metOn().stoppingIn(container,
                        how == HowAClosureIsApplied.UNTIL_ONE_HOLDS ? answered
                                : conditions.denied(answered));
            }
        };
    }

    /**
     * {@code around}, inside a closure made on elements of {@code containers} nothing here says
     * which of: of each container that is a position of the input, or of whichever a reading
     * chooses an element of where one is not — or where which containers is not said at all.
     */
    private static ElementsMetOn notSaid(ElementsMetOn around, List<Denotation> containers,
                                         InputReading read, ReadingGap why) {
        List<TermPath> positions = new ArrayList<>();
        for (Denotation each : containers) {
            if (!(each.at().pathOf(each.value(), read.newtypes())
                    instanceof PathResolution.At(TermPath container))) {
                return around.notSaidAnywhere(why);
            }
            positions.add(container);
        }
        if (positions.isEmpty()) {
            return around.notSaidAnywhere(why);
        }
        ElementsMetOn out = around;
        for (TermPath container : positions) {
            out = out.notSaidOf(container, why);
        }
        return out;
    }

    /**
     * What each thing an element was kept by states, read where it was decided
     * ({@link WhatConditionsState#kept}). One this cannot read is said as one it did not read, and
     * not as one that holds: an application it decides is one a run may not make.
     */
    private static List<Proposition> keptBy(List<ReadMeaning.Occurrence.Kept> keptWhere,
                                            InputReading read) {
        WhatConditionsState conditions = WhatConditionsState.of(read);
        return keptWhere.stream().map(kept -> conditions.kept(kept, read)).toList();
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
                WhatConditionsState conditions = WhatConditionsState.of(read);
                Proposition stated = conditions.truth(condition, one.reads(), read).proposition();
                Proposition past = holding ? stated : conditions.denied(stated);
                return Proposition.leavesSomethingUnread(past)
                        && pastOnTheFirstStep(condition, holding, one, read) ? one
                        : new Application(one.reads(), WhereAnApplicationIsMade.past(
                                one.reached(), past), one.carriedIntoTheFirst(), one.metOn());
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
        return WhatConditionsState.of(read).truth(condition, first, read).proposition()
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
            return new Application(one.reads(), one.reached(), carried, one.metOn());
        }).toList());
    }

    /**
     * The same applications past {@code step}, which is no step into an arm.
     *
     * <p>An arm is entered by name ({@link #choosing}), with what entering it states, so every
     * application is reached under that as well. Entered here, an arm would add nothing to any of
     * them, and an application taking another arm would be read as one that reached this one — so
     * it is refused rather than answered.
     */
    default ClosureApplications entering(ScopeStep step, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        if (step instanceof ScopeStep.Chosen) {
            throw new IllegalStateException("an arm is entered by naming what entering it states,"
                    + " and was entered by a step: " + step);
        }
        return moved(reads -> reads.entering(step, symbols, newtypes));
    }

    /** The same applications with {@code binder} standing for {@code value}. */
    default ClosureApplications and(Core.Binder binder, Core value) {
        return moved(reads -> reads.and(binder, value));
    }

    /**
     * The applications that enter the arm {@code decidedBy} decides, inside it, each reached under
     * what entering the arm states on it as well.
     *
     * <p>An application handed a value of a case the arm does not take never enters it, so it is
     * left out rather than read in an arm it does not reach. Where none enters, no run reaches
     * what is in the arm ({@link None}).
     *
     * <p>One that may enter it enters it where what {@code entered} states of it holds, read in
     * that application's names: a run making the application on one value and taking another arm
     * did not get to what is in this one. Null where nothing is added: an {@code if} whose
     * condition was already {@link #taking taken}, or an arm entered by a step that says no more
     * than which arm it is ({@link #entering}).
     */
    default ClosureApplications choosing(Choice.Decides decidedBy, Symbols symbols,
                                         DeclarationNewtypes newtypes,
                                         Function<InputReads, Proposition> entered) {
        if (!(this instanceof Each(var each))) {
            return this;
        }
        List<Application> entering = each.stream()
                .filter(one -> mayEnter(one, decidedBy, symbols, newtypes))
                .map(one -> new Application(one.reads().choosing(decidedBy, symbols, newtypes),
                        entered == null ? one.reached()
                                : WhereAnApplicationIsMade.past(one.reached(),
                                        entered.apply(one.reads())),
                        one.carriedIntoTheFirst(), one.metOn()))
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
                            one.carriedIntoTheFirst(), one.metOn()))
                    .toList());
            case Outside _, NotSaid _, None _ -> this;
        };
    }
}
