package souther.compiler.reading;

import souther.compiler.check.Choice;
import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Naming;
import souther.compiler.flow.Truth;
import souther.compiler.flow.Provenance;
import souther.compiler.flow.UnwordedTruth;
import souther.compiler.flow.WayWritten;
import souther.compiler.inputs.CaseCompared;
import souther.compiler.inputs.ComparedNumber;
import souther.compiler.inputs.ComparedNumbers;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.InputTruth;
import souther.compiler.inputs.WhatAConditionRuns;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The conditions along a path, said of the input positions they are about and of the places a run
 * that took them would be seen at.
 *
 * <p>What a group is composed against, and the only part of reading a body that the numbering has
 * anything to do with. Nothing here decides whether an expression arrives at a value or what a value
 * comes to: a condition this has no words for comes back as null, the reading marks the path
 * {@link souther.compiler.flow.Completeness#PARTIAL}, and the arm or the way is still there. That is
 * the whole of the separation — before it, a comparison the plan could not place was read as a
 * comparison with no value, and everything standing under it went with it.
 *
 * <p>A value per position and not one object walked along: what a name reads widens inside a
 * {@code let}, so {@link #entering} answers a new one and the reading holds each where it belongs.
 */
final class CoverageNaming implements Naming<Outcome> {

    /**
     * How many ways one value is read as being settled before the reading gives up on enumerating
     * them.
     *
     * <p>A product taken at one node. What bounds how many ways in a position is read under is a
     * different bound on a different product, and the two multiply with the nesting of a body.
     */
    static final int MOST_OUTCOMES = 64;

    private final CoverageSites.Plan plan;
    private final Symbols symbols;

    /** Which declarations wear one value, which is what says whether reading a field reaches
     *  somewhere else ({@link souther.compiler.check.Location#isStep}). */
    private final DeclarationNewtypes newtypes;
    private final InputReads reads;

    /** What each comparison of this body is about, read once and shared with whatever else asks. */
    private final ComparedNumbers numbers;

    CoverageNaming(CoverageSites.Plan plan, Symbols symbols, DeclarationNewtypes newtypes,
                   InputReads reads, ComparedNumbers numbers) {
        this.plan = plan;
        this.symbols = symbols;
        this.newtypes = newtypes;
        this.reads = reads;
        this.numbers = numbers;
    }

    /** What a name reads here, which a caller walking the body needs for its own naming. */
    InputReads reads() {
        return reads;
    }

    @Override
    public Outcome nowhere() {
        return new Outcome(List.of());
    }

    @Override
    public Outcome join(Outcome held, Outcome more) {
        List<Decision> both = merge(held.holds(), more.holds());
        return both == null ? null : new Outcome(both);
    }

    // The environment moves and the reading of the comparisons does not: what a name reads here is
    // this naming's own, and what each comparison came to is one answer for the whole body.
    @Override
    public CoverageNaming entering(ScopeStep step) {
        InputReads inside = reads.entering(step, symbols, newtypes);
        return inside == reads ? this : new CoverageNaming(plan, symbols, newtypes, inside, numbers);
    }

    /**
     * That {@code comparison} came out {@code held}, said of the position it is about, or null where
     * this cannot say which position that is or where no run through it could be recorded.
     *
     * <p>The comparison and not the arm. A condition stops as soon as it is settled, so under
     * {@code A && B} the arm taken when the condition fails is reached both by a value that made
     * {@code B} false and by one that never evaluated {@code B}: a row is steered by getting the
     * comparison to answer, which no arm records.
     */
    @Override
    public Outcome side(Core value, boolean held) {
        if (!(Core.withoutStanding(value) instanceof Core.Binary comparison)) {
            // A position holding a truth comes out both ways and the plan places no comparison at
            // it, so there is nothing here to say. The fork on it is named where the way in is.
            return null;
        }
        // The one reading of this comparison, which is the reading whatever admitted the way used.
        // Read again here, the decision would be said of a number the admission never saw. A case
        // of a sum held equal to the value is read as which case it is, as the admission reads it.
        CaseCompared compared = numbers.caseOf(comparison, reads);
        ComparedNumber drawn = compared == null ? numbers.of(comparison, reads) : null;
        if (compared == null && drawn == null) {
            return null;
        }
        // Which construct of the model the decision is of. An application answering here comes
        // first: the comparison is then the code of the operation it applies, which the model
        // states nothing of, and the rule the author wrote — and drew a line by — is the
        // application. Where none does, the comparison is the construct.
        ControlPlace.Outcome outcome = plan.applicationAnsweringAt(comparison)
                .flatMap(application -> plan.outcomeOf(application, held))
                .or(() -> outcomeAt(plan, comparison, held))
                .orElse(null);
        if (outcome == null) {
            return null;
        }
        Condition condition = compared != null ? casesLeft(compared, held)
                : new Condition.Side(drawn.term(), outcome.occurrence(), held, lineOf(drawn));
        if (condition == null) {
            return null;
        }
        // The condition and the claim are about one comparison, so they are read off one value. The
        // place the claim is made at says which comparison it is a way out of; asked of the node
        // instead, the two halves of this decision would be two answers, and a decision whose
        // condition named one comparison and whose claim was recorded at another is one nothing
        // here reads both halves of to notice.
        return ControlClaim.of(outcome)
                .map(claim -> one(new Decision(condition, claim)))
                .orElse(null);
    }

    /**
     * What a value of a sum compared with one of its cases coming out {@code held} leaves it: the
     * cases, as an arm of a {@code match} on it leaves them ({@link CaseCompared}). A run is
     * steered there by which case it hands in, and the order the cases are declared in has nothing
     * to do with it.
     *
     * <p>Null where it leaves no case. No value comes out that way; where the declarations were
     * not read to rule the way out, it is left unnamed, which keeps what it is about open, rather
     * than named as a set of cases no value is.
     */
    private static Condition casesLeft(CaseCompared compared, boolean held) {
        List<TypeSymbol> left = compared.leavesWhere(held);
        return left.isEmpty() ? null : new Condition.Case(compared.at(),
                left.stream().map(TypeSymbol::name).toList());
    }

    /**
     * The place {@code comparison} coming out {@code held} is recorded at, or empty where the plan
     * records no run through it.
     *
     * <p>The one way from a comparison of the tree that runs to where a run is seen making it, for
     * every naming of a body that says what a run would be seen doing.
     */
    static Optional<ControlPlace.Outcome> outcomeAt(CoverageSites.Plan plan,
                                                    Core.Binary comparison, boolean held) {
        return plan.comparisons().occurrenceAt(comparison)
                .filter(plan::instruments)
                .flatMap(site -> plan.outcomeOf(site, held));
    }

    /** What {@code drawn} places on its number, where its other side is a value the number's order
     *  writes and its operator states something. */
    private static Optional<Condition.Side.Line> lineOf(ComparedNumber drawn) {
        return drawn.at() != null && drawn.placed() instanceof ComparisonClaim claim
                ? Optional.of(new Condition.Side.Line(drawn.at(), claim)) : Optional.empty();
    }

    /** Which case of the union this arm is, said of the position matched on where there is one, or
     *  null where no run through the arm could be recorded. */
    @Override
    public Outcome matchCase(Core.Match match, int part) {
        ControlPlace.Arm place = armPoint(match, part);
        ControlClaim claim = claimAt(place);
        if (claim == null) {
            return null;
        }
        Condition.Case taken = caseOf(match, part);
        return one(new Decision(taken == null ? new Condition.Arm(place.arm(),
                Condition.Arm.decidingConstructOf(match.scrutinee())) : taken, claim));
    }

    /**
     * What a run down arm {@code part} of {@code match} takes of the inputs, or null where the
     * scrutinee is at no position.
     *
     * <p>Whether or not a run there is one anything watches. What an arm takes of the inputs is the
     * case it is written for, which an arm nothing instruments — one that answers nothing — has as
     * much as any other; what it lacks is a claim a run could be seen making, which is the other half
     * of a {@link Decision} and not this.
     */
    public Condition.Case caseOf(Core.Match match, int part) {
        // What a fork is named by is the position it is on, and a scrutinee at none names nothing —
        // which is also what a scrutinee this reading did not follow leaves to name it with.
        TermPath at = switch (reads.pathOf(match.scrutinee(), newtypes)) {
            case PathResolution.At(var stands) -> stands;
            case PathResolution.NotAPosition _ -> null;
            // A name that only may stand at a position names no one position for a fork to be on,
            // and a name built out of the ones it may be would be a place no reader could look up.
            case PathResolution.MayStandAt _ -> null;
        };
        if (at == null) {
            return null;
        }
        return Condition.Case.of(at, match.cases().get(part));
    }

    /**
     * That a run went down arm {@code part}, where nothing said which comparison sent it there.
     *
     * <p>What the reading falls back on. Where the condition's ways can be enumerated they are what
     * names the way in, on the comparisons a row is steered by; this is the answer for a condition
     * whose ways cannot all be written down, and it is the answer every fork used to get.
     *
     * <p>An arm places at no class of any input, so a group offered under one of these goes. That it
     * is here at all is what says the reading found a way in it could not name.
     *
     * <p>An attempt's arms are always this: whether the invariant held is decided by nothing
     * written in the body, so there is no position to say it of and the arm is what names it.
     */
    @Override
    public Outcome forkArm(Core fork, int part) {
        ControlPlace.Arm place = armPoint(fork, part);
        ControlClaim claim = claimAt(place);
        if (claim == null) {
            return null;
        }
        Condition what = switch (Choice.decidingArm(fork, part)) {
            case Choice.Decides.ACondition(Core.If iff, boolean holding) -> {
                Condition.Case truth = truthOf(iff.cond(), holding);
                yield truth == null ? new Condition.Arm(place.arm(),
                        Condition.Arm.decidingConstructOf(iff.cond())) : truth;
            }
            // Whether the invariant held is decided by nothing written in the body.
            case Choice.Decides.ItWasBuilt _ -> new Condition.Arm(place.arm(), Optional.empty());
            case Choice.Decides.ItDeparted _ -> new Condition.Arm(place.arm(), Optional.empty());
            // Named by matchCase, which is asked of the match and not of a fork in general.
            case Choice.Decides.ACase _ -> throw new IllegalStateException(
                    "a case of a match at " + fork.pos() + " was asked of as an arm of a fork");
            case Choice.Decides.ByArgumentRelations _ -> throw new IllegalStateException(
                    "an operation the library defines by cases at " + fork.pos()
                            + " was asked of as an arm of a fork, and no walk enters one");
        };
        return one(new Decision(what, claim));
    }

    /**
     * The way, and where it says less than that the condition came out the arm's way, each part of
     * the condition a run down the arm brought out a known way: a {@code Bool} position holding the
     * truth it came to, seen at the arm, and a comparison as it is seen anywhere.
     *
     * <p>What the way left out is then the positions' truths, which come out a way at no construct
     * the plan places; the arm a run took says which, and the positions are what a row is composed
     * at. Only where every part is one of those and came out a way the arm says
     * ({@link WhatAConditionRuns}): a part this has no words for is no position to say anything
     * of, and a part the arm leaves open — under {@code a || b} holding, which of the two did — is
     * nothing the arm says. There this has no words for the arm, and the way is the condition's.
     */
    @Override
    public Outcome seenAtTheArm(Core.If fork, int part, Arrival<Outcome> onlyWay) {
        return atTheArm(fork, part, onlyWay) instanceof WayWritten.As<Outcome>(Outcome path)
                ? path : null;
    }

    /**
     * The way as a run down the arm is seen taking it, read as {@link #seenAtTheArm} reads the one
     * way in — and here the parts the arm says came out a way are the ones this way says, with the
     * arm, came out that way.
     *
     * <p>A way that says the left of an {@code &&} held says the right ran, and with the arm taken on
     * the condition failing, that the right failed: the truth there the walk had no words for is
     * then as known as it is on the one way in. A way that says the left failed says the right never
     * ran, and it reads nothing of it. Where the way says neither, the arm cannot say which of the
     * ways a run seen there came by, and this has no words for the way.
     *
     * <p>Written down, and not yet witnessed. A truth said here is seen at the arm, and the arm is
     * passed by a run on any of the ways into it: whether what a run is seen doing tells this way
     * from the others is a question about all of them together, which is the reader's
     * ({@link CoverageRead}).
     */
    @Override
    public WayWritten<Outcome> oneOfTheWaysIn(Core.If fork, int part, Arrival<Outcome> way) {
        return atTheArm(fork, part, way);
    }

    /** Told apart by the claims each decision on them is made with, which are what a run is held
     *  to ({@link ControlClaim#toldApart}). */
    @Override
    public boolean toldApart(List<Outcome> ways) {
        return ControlClaim.toldApart(ways.stream()
                .map(way -> way.holds().stream().map(Decision::claims).toList())
                .toList());
    }

    /**
     * {@code way}, one of the ways into arm {@code part} of {@code fork}, with what it left out said
     * as the arm sees it; or that the arm does not say it; or that what the way and the arm say
     * together settles one decision two ways, which no run does.
     *
     * <p>What the arm says is each part of the condition a run on the way down the arm brought out a
     * known way ({@link WhatAConditionRuns#alongAWay}): known from the arm alone where the condition
     * came out the way that settles every part, and from what the way itself says of the parts it
     * went through otherwise — a comparison it named, and a truth it had no words for with the way
     * that truth came out ({@link Provenance#unworded}).
     */
    private WayWritten<Outcome> atTheArm(Core.If fork, int part, Arrival<Outcome> way) {
        if (way.value() != Truth.UNREAD && way.isComplete()) {
            return new WayWritten.As<>(way.path());
        }
        ControlClaim claim = claimAt(armPoint(fork, part));
        if (claim == null) {
            return new WayWritten.NoWords<>();
        }
        Map<Core, Boolean> unworded = new IdentityHashMap<>();
        for (UnwordedTruth each : way.provenance().unworded()) {
            InputTruth.Asked asked = InputTruth.asked(each.truth(), each.held(), reads, symbols,
                    newtypes);
            // A name and what it stands for are one truth, and one truth that came out both ways
            // on one way is no run.
            Boolean already = unworded.put(asked.value(), asked.holding());
            if (already != null && already != asked.holding()) {
                return new WayWritten.NoRun<>();
            }
        }
        WhatAConditionRuns ran = WhatAConditionRuns.alongAWay(fork.cond(), part == 0,
                each -> told(way.path(), unworded, each), reads, symbols, newtypes);
        if (!ran.whole()) {
            return new WayWritten.NoWords<>();
        }
        Outcome out = way.path();
        for (WhatAConditionRuns.Settled each : ran.settled()) {
            // A way that says a part came out the other way from the one the arm says does not
            // come here.
            Boolean came = unworded.get(each.part());
            if (came != null && came != each.held()) {
                return new WayWritten.NoRun<>();
            }
            // Each part read where it was written, which behind a name is not where the fork is.
            InputTruth truth = InputTruth.of(each.part(), each.held(), each.reads(), symbols,
                    newtypes);
            if (truth != null) {
                // Two reads of one position that came out two ways are one decision settled two
                // ways, which is no path ({@link #join}).
                out = join(out, one(new Decision(new Condition.Case(truth.at(),
                        List.of(truth.held() ? "true" : "false")), claim)));
                if (out == null) {
                    return new WayWritten.NoRun<>();
                }
            } else if (!named(way.path(), each)) {
                return new WayWritten.NoWords<>();
            }
        }
        return new WayWritten.As<>(out);
    }

    /**
     * How {@code way} says {@code part} came out: a comparison by the claim the walk named it with
     * ({@link #named}), and a truth it had no words for by the way it came out.
     */
    private static Optional<Boolean> told(Outcome way, Map<Core, Boolean> unworded, Core part) {
        Boolean truth = unworded.get(part);
        if (truth != null) {
            return Optional.of(truth);
        }
        if (!(Core.withoutStanding(part) instanceof Core.Binary comparison)
                || comparison.occurrence() == null) {
            return Optional.empty();
        }
        for (Decision each : way.holds()) {
            if (each.claims().at() instanceof ControlPlace.Outcome outcome
                    && outcome.occurrence().equals(comparison.occurrence())) {
                return Optional.of(outcome.held());
            }
        }
        return Optional.empty();
    }

    /**
     * Whether {@code way} already says {@code part} came out the way it did — a comparison the
     * walk named where it read it.
     *
     * <p>Asked of the way and not read again here. The walk read the comparison once, under what
     * its names read where it stands, and the way is a way the condition came out: a comparison on
     * it the walk had words for is on it, and one it had none for is not, which is a part this has
     * no words for either.
     *
     * <p>Found by the claim and not by the condition. A comparison comes out a side of its number
     * or a set of cases ({@link #side}), and either way its claim is that it came out the way it
     * did where it was stated.
     */
    private static boolean named(Outcome way, WhatAConditionRuns.Settled part) {
        if (!(Core.withoutStanding(part.part()) instanceof Core.Binary comparison)
                || comparison.occurrence() == null) {
            return false;
        }
        for (Decision each : way.holds()) {
            if (each.claims().at() instanceof ControlPlace.Outcome outcome
                    && outcome.occurrence().equals(comparison.occurrence())
                    && outcome.held() == part.held()) {
                return true;
            }
        }
        return false;
    }

    /** What {@code cond} coming out {@code holding} says a {@code Bool} position holds, or null
     *  where it says nothing of one ({@link InputTruth}). */
    private Condition.Case truthOf(Core cond, boolean holding) {
        InputTruth truth = InputTruth.of(cond, holding, reads, symbols, newtypes);
        return truth == null ? null
                : new Condition.Case(truth.at(), List.of(truth.held() ? "true" : "false"));
    }

    @Override
    public Outcome wentOn(Core.Binary operator, Outcome left, Arrival<Outcome> right) {
        return left;
    }

    @Override
    public Outcome stoppedShort(Core.Binary operator, Outcome left) {
        return left;
    }

    @Override
    public int mostArrivals() {
        return MOST_OUTCOMES;
    }

    /**
     * The place arm {@code part} of {@code fork} is, or null where the plan numbered no such arm.
     *
     * <p>Which arm it is comes back with it, so a reading that has to name the decision without a
     * position names it off the place it has already asked for. Asked again of the fork, the answer
     * would be this plan's arms read a second time to say what the first read already said.
     */
    private ControlPlace.Arm armPoint(Core fork, int part) {
        ControlPlace.Arm[] arms = plan.armsOf(fork);
        return arms == null || part >= arms.length ? null : arms[part];
    }

    /** What a run through {@code place} would be seen doing, and null where nothing records one. */
    private static ControlClaim claimAt(ControlPlace.Arm place) {
        return place == null ? null : ControlClaim.of(place).orElse(null);
    }

    private static Outcome one(Decision decision) {
        return new Outcome(List.of(decision));
    }

    /**
     * Both sets of conditions, or null where between them they settle one decision two ways.
     *
     * <p>One rule for every place two of these are put together: the parts of a value, a way in held
     * to the way in above it, the left of an operator that stops early held to what runs after it. A
     * decision read twice is one decision, and one settled two ways is no path.
     */
    static List<Decision> merge(List<Decision> holds, List<Decision> more) {
        List<Decision> both = new ArrayList<>(holds);
        for (Decision each : more) {
            if (both.contains(each)) {
                continue;
            }
            if (disagrees(both, each)) {
                return null;
            }
            both.add(each);
        }
        return both;
    }

    /**
     * Whether {@code added} settles a decision the conditions already settle the other way.
     *
     * <p>The same decision and a different way out of it, which is two things and not one. A decision
     * named twice and settled the same way is one run doing one thing twice over —
     * {@code if a then (if a then …)} is written as two forks and no row takes one of them without
     * the other — and reading that as a contradiction would take away a path the body has.
     *
     * <p>Which decision it is is not which place a run is recorded at. Two forks on one flag are two
     * places and one decision, so what is compared is what the condition is about and never the claim
     * beside it — and what the conditions are about is theirs to say ({@link Condition#excludes}).
     */
    private static boolean disagrees(List<Decision> holds, Decision added) {
        for (Decision already : holds) {
            if (added.constrains().excludes(already.constrains())) {
                return true;
            }
        }
        return false;
    }
}
