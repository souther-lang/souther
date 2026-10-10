package souther.compiler.partition;

import souther.compiler.check.Choice;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.semantics.HowAClosureIsApplied;

import java.util.ArrayList;
import java.util.List;
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
     * One application.
     *
     * @param reads   the names in force at it, with the value it was handed in place of the
     *                parameter
     * @param reached what has to hold for a run to make it
     */
    record Application(InputReads reads, Proposition reached) {

        public Application {
            Objects.requireNonNull(reads, "an application is read in some names");
            Objects.requireNonNull(reached, "and is made under something");
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
                    List.of(new Application(reads, WhereAnApplicationIsMade.nothingAsked())),
                    read, true);
            case Each(var outer) -> applied(block, step, outer, read, false);
            case NotSaid _ -> this;
        };
    }

    /**
     * The applications of {@code block} made inside each of {@code outer} — and where the block is
     * handed nothing written out, each of {@code outer} past the step into it, or nothing at all
     * where {@code outer} stands for being inside no closure.
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
            switch (Pullback.applicationsOf(block, around.reads(), symbols, newtypes)) {
                case InputReads.Applications.Each(var each, var how) -> {
                    handed = true;
                    List<Proposition> answers = how == HowAClosureIsApplied.TO_EVERY_ELEMENT ? null
                            : each.stream().map(one -> Pullback.ofATruth(block.body(), one, read,
                                    Optional.empty()).proposition()).toList();
                    List<Proposition> reached = WhereAnApplicationIsMade.reached(answers,
                            each.size(), how, around.reached());
                    for (int at = 0; at < each.size(); at++) {
                        out.add(new Application(each.get(at), reached.get(at)));
                    }
                }
                case InputReads.Applications.NoneHanded _ -> {
                    List<List<TermPath>> takenFrom = containersHeld(block, around.reads(), read);
                    asked |= !takenFrom.isEmpty();
                    out.add(new Application(around.reads().entering(step, symbols, newtypes),
                            WhereAnApplicationIsMade.whereTheContainersHoldSomething(
                                    around.reached(), takenFrom)));
                }
                case InputReads.Applications.Unsaid _,
                     InputReads.Applications.MoreThanAreRead _ -> {
                    return new NotSaid();
                }
            }
        }
        return handed || asked || !outside ? new Each(out) : OUTSIDE;
    }

    /**
     * For each parameter of {@code block} an operation hands something a container holds, the
     * positions of the input those containers stand at.
     *
     * <p>A parameter is left out where some container it may be handed something from stands at no
     * position: a run may be inside the closure by that one with every other empty, so saying the
     * rest hold something would be saying more than is known.
     */
    private static List<List<TermPath>> containersHeld(Core.Block block, InputReads reads,
                                                       InputReading read) {
        List<List<TermPath>> out = new ArrayList<>();
        for (List<Denotation> containers : reads.containersHandingTheElements(block)) {
            List<TermPath> positions = new ArrayList<>();
            for (Denotation container : containers) {
                Optional<TermPath> at = Pullback.positionHoldingWhatItHolds(container, read);
                if (at.isEmpty()) {
                    positions = null;
                    break;
                }
                positions.add(at.get());
            }
            if (positions != null) {
                out.add(List.copyOf(positions));
            }
        }
        return out;
    }

    /**
     * Whether what holds on the way to a place inside these is said of each application. Where it
     * is, a condition met inside the closure goes onto what each application is reached under,
     * read in that application's names, and not onto the way every application shares — read
     * there, it would be read with the parameter standing for any of the values at once.
     */
    default boolean saysWhatStandsInIt() {
        return this instanceof Each;
    }

    /** The same applications past {@code condition} coming out {@code holding} on each of them. */
    default ClosureApplications taking(Core condition, boolean holding, InputReading read) {
        return switch (this) {
            case Each(var each) -> new Each(each.stream().map(one -> {
                Proposition stated = Pullback.ofATruth(condition, one.reads(), read,
                        Optional.empty()).proposition();
                return new Application(one.reads(), WhereAnApplicationIsMade.past(one.reached(),
                        holding ? stated : stated.denied()));
            }).toList());
            case Outside _, NotSaid _ -> this;
        };
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
     * left out rather than read in an arm it does not reach. Where none enters, what is in the arm
     * is read once as it stands, as it would be in a closure whose applications are not said.
     */
    default ClosureApplications choosing(Choice.Decides decidedBy, Symbols symbols,
                                         DeclarationNewtypes newtypes) {
        if (!(this instanceof Each(var each))) {
            return this;
        }
        List<Application> entering = each.stream()
                .filter(one -> mayEnter(one, decidedBy, symbols, newtypes))
                .map(one -> new Application(one.reads().choosing(decidedBy, symbols, newtypes),
                        one.reached()))
                .toList();
        return entering.isEmpty() ? new NotSaid() : new Each(entering);
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
                    .map(one -> new Application(step.apply(one.reads()), one.reached()))
                    .toList());
            case Outside _, NotSaid _ -> this;
        };
    }
}
