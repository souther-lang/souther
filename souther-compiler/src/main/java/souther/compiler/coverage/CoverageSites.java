package souther.compiler.coverage;

import souther.compiler.check.Comparison;
import souther.compiler.core.Core;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CoverageConstruct;
import souther.compiler.types.CoverageOrigin;

import java.util.ArrayList;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.OptionalInt;
import java.util.Map;

/**
 * The arms of a behavior's body that an {@code example} row can be in or not in.
 *
 * <p>What this counts is <em>branch-arm coverage</em>, and calling it anything larger would overstate
 * it. Passing through all four arms of
 *
 * <pre>if A { if B { X } else { Y } } else { Z }</pre>
 *
 * does not mean the interactions between A and B were tried, nor that every reachable path was. Branch
 * coverage is a lower bound on covering the paths a body has, not the same thing, and a report that
 * says "code paths" invites the author to stop looking.
 *
 * <p>An arm that answers nothing gets no site. Reaching one is already an error ({@code E1911}), so a
 * probe there would leave every correct model permanently one arm short and make the denominator lie.
 * Which arms those are is {@link NormalReturn}'s answer, so an arm whose every path ends in an
 * {@code unreachable} is as much not an arm as one written as a bare {@code unreachable}. An
 * invariant clause gets none either: it is a property of a type, not a fork in this body, and whether
 * the rows reach its edges is a different measure asked another way.
 *
 * <p>A {@code guard … else} and a comprehension's condition are both an {@code if} by the time they
 * get here, so the walk has one case for the three of them — and what they are is not read off that
 * case. Which construct the author wrote is carried from where the source was read
 * ({@link souther.compiler.types.CoverageConstruct}), and what one way through it means is a
 * {@link SourceOutcome} beside it. Deciding either from the shape of the lowered node is answering a
 * question about the source out of the tree that runs, which is how a comprehension came to be
 * reported as a {@code guard} with a {@code then} arm.
 *
 * <p>Helper bodies are not walked: a non-recursive helper is already inlined into the body that uses it,
 * and a recursive one is a shared method rather than a fork in any one behavior.
 */
public final class CoverageSites {

    /**
     * Which rule one occurrence of a fork decides by.
     *
     * <p>Beside the fork's own construct in what an arm is counted under. A non-recursive helper is
     * spliced into each body that calls it, and the copies are one arm the author wrote — which
     * holds while the helper decides for itself. Where the caller hands the rule in, each call
     * decides by a different rule, and those are different things to cover: a row through one of
     * them establishes nothing about the next.
     *
     * <p>Which of the two a fork is, is {@link DecisionSources}'s answer, read off the declaration
     * that wrote the fork. Not read off the condition standing here: after expansion the argument
     * the call site supplied is standing where the parameter was, whether it was the rule or what
     * the rule reads, and no description of what is left can tell those apart. Two descriptions
     * that came out alike were counted as one obligation, and a rule nothing exercised was reported
     * as covered.
     */
    private static DecidedBy decidedAt(CoverageOrigin fork, List<BindingOwner> within,
                                       DecisionSources decisions, SuppliedRules supplied) {
        if (!(decisions.at(fork) instanceof DecisionSource.Supplied by)) {
            return DecidedBy.THE_DECLARATION;
        }
        // The rules this copy was handed, asked of the copy it is and of the parameters the
        // declaration named. Both are answers somebody else already had: which copy this is, the
        // elaboration stamped on the fork; what was handed to each parameter, the call site
        // recorded. Worked out here instead — from whatever names the fork's own subtree happens to
        // hold — a fork deciding by a rule that reduced to a constant is a fork with nothing to ask
        // about, and a combinator nested inside one answered for the fork above it.
        // The copy of the declaration that wrote this fork, which is not always the innermost copy
        // the fork stands in: a helper's own fork can be written inside a block it hands to
        // something else, and what is nearest round it is then that something else's. Which copy is
        // meant is a copy of that declaration — asked by the names of its parameters instead, a copy
        // of anything else that spells one the same way answers first, and it answers with its own
        // rule.
        for (BindingOwner owner : within) {
            // Both sides say which declaration by the name this module reaches it under, which is
            // one name because both took it from one place: the reading walked the table of what
            // this body can reach, and the expansion looked its callee up in that same table under
            // the name the call resolved to. A second way of saying which declaration -- one side
            // naming it, the other spelling it -- would agree until a declaration came to be reached
            // under two names, and nothing would say which of them a copy was of.
            if (!by.declaration().equals(supplied.declarationOf(owner))) {
                continue;
            }
            List<SuppliedRules.RuleIdentity> rules = new ArrayList<>();
            for (String parameter : by.parameters()) {
                SuppliedRules.RuleIdentity rule = supplied.at(owner, parameter);
                if (rule != null) {
                    rules.add(rule);
                }
            }
            if (rules.size() == by.parameters().size()) {
                return new DecidedBy.BySupplied(rules);
            }
        }
        return DecidedBy.NOT_SAID;
    }

    /**
     * What stands in an arm's place where the arm answers nothing.
     *
     * <p>The arms of a node are handed to the emitter as an array it indexes by the arm's position, so
     * an arm without a probe has to keep its place. Compacting the array would move every arm after
     * it down one and the emitter would light its neighbour's probe — a hit recorded against an arm
     * nothing ran, which no count can be told apart from a real one.
     */
    public static final int NO_SITE = -1;

    /**
     * What a row is owed for, which is not the same as where one runs.
     *
     * <p>A non-recursive helper is spliced into each body that calls it, so one arm the author wrote
     * is several arms in the tree that runs. Each of those is emitted and probed on its own, and each
     * is asked separately whether anything can reach it — so the occurrences stay apart everywhere
     * below. What they are not is several things to write rows for: covering the same arm through a
     * second call site establishes nothing the first did not. This is the key those occurrences are
     * one under.
     *
     * <p>Per behavior, because the measurement is per behavior. Two behaviors calling one helper each
     * owe its arms, and a row written for one of them is not a row written for the other.
     *
     * @param part which arm of the fork — its place among the fork's arms. Always zero for a
     *             comparison, whose origin is its own rather than the fork's: a comparison is one
     *             construct, and what a fork holds several of is arms
     */
    public record Obligation(String behavior, CoverageOrigin origin, int part,
                             DecidedBy decided) {}

    /**
     * One outcome of one construct, as it stands in the tree that runs.
     *
     * <p>Two halves and one meaning. {@link #obligation} carries the construct the source wrote, and
     * {@link #outcome} what this way through it means; neither says the other, so nothing here can
     * hold two answers about one construct. Which of them the pair comes to is {@link #name}, and
     * that is as far as this goes — a condition holding is a {@code then} under an {@code if} and the
     * rest of the block under a {@code guard}, and both of those are said in a language, by whoever
     * has a reader in front of them.
     *
     * @param outcome     what this way through the construct means, in the source's terms
     * @param at          where the arm is written, as a report may say it. A {@link Citation} and
     *                    not a place, because an arm of a body spliced in from out of sight is at a
     *                    call in the caller's file and is not written there — a report handed the
     *                    coordinate said it was, in both of its renderings
     * @param index       what identifies it in this run — the probe number, and what a hit set holds.
     *                    One per occurrence: the emitter lights this one, and the reachability
     *                    analysis proves things about this one
     * @param ordinal     where it comes in its behavior, for display
     * @param obligation  what a row would be owed for, which several occurrences share
     */
    public record Site(String behavior, SourceOutcome outcome, Citation at,
                       int index, int ordinal, Obligation obligation) {

        public Site {
            // The pair is what carries the meaning, so the pair is what is checked. Not every
            // combination is a construct of the language — a comprehension attempts no construction,
            // a `match` settles no condition — and a walk that put an outcome on the wrong construct
            // is the defect this whole value exists to make impossible.
            OutcomeName.of(obligation.origin().kind(), outcome);
        }

        /** What the author wrote this an outcome of. */
        public CoverageConstruct construct() {
            return obligation.origin().kind();
        }


        /** What a reader is told this is, which the two halves settle together. */
        public OutcomeName name() {
            return OutcomeName.of(construct(), outcome);
        }

        /** Whether this is one of the arms a branch measure counts. */
        public boolean isArm() {
            return outcome.isArm();
        }
    }

    /**
     * The two arms of one {@code if}, so that a threshold read off its condition can ask whether the
     * comparison was ever evaluated.
     *
     * <p>Reaching a value is not reaching a comparison. A row can hand a behavior the exact boundary
     * value and never get to the guard that cares about it, because an earlier branch went the other
     * way — so a boundary drawn by a guard is met only by a row that also lit one of these.
     *
     * <p>Either side may be {@link #NO_SITE}, where that arm answers nothing: the comparison was
     * still evaluated to reach the arm beside it. An {@code if} whose arms both answer nothing has no
     * {@code GuardRef} at all — there is nothing left for a row to reach, and a reference with two
     * absent sides would report the line as never met however the model is exercised.
     *
     * @param at the fork's own place. A coordinate and not a reference over one: a reference
     *           carries a source beside the one the coordinate has, and a walk over one module
     *           pairs its own with a position from a helper another module wrote. Nothing reads
     *           the pair, and a value that can hold two answers about one place is one a reader
     *           can pick the wrong half of.
     */
    public record GuardRef(String behavior, CoverageOrigin origin, DecidedBy decided,
                           int siteIndexThen, int siteIndexElse, SourcePos at) {

        /** The fork this is one occurrence of. Two calls of one helper give two of these, and a line
         * drawn on the condition is one line however many of them there are. */
        public Obligation fork() {
            return new Obligation(behavior, origin, 0, decided);
        }
    }

    /**
     * Every site of a module, and how to find the ones belonging to a node.
     *
     * <p>{@code byNode} is keyed by identity. Core nodes are records, so two arms that look the same
     * are equal, and a value-keyed map would hand the emitter the wrong arm's probe. The instances
     * here must be the ones the emitter is walking — the same answer, not an equal one.
     */
    public record Plan(List<Site> sites, List<GuardRef> guards, IdentityHashMap<Core, int[]> byNode,
                       IdentityHashMap<Core, Integer> byComparison,
                       IdentityHashMap<Core, ControlPointId.ArmOccurrence[]> armsByNode,
                       IdentityHashMap<Core, Integer> controlByComparison,
                       java.util.Set<Core> mayRepeat,
                       IdentityHashMap<Core, ForkOccurrence> forkByNode,
                       ComparisonCatalog comparisons) {

        public Plan {
            // Every number is of a comparison this plan's catalog holds. Two things go wrong
            // without it and they are not the same thing.
            //
            // What a number means to the emitter is "copy the value this node left on the stack",
            // so a number on anything but a comparison is a copy of something else — half a `long`
            // where the node was arithmetic, or the whole condition where it was an `&&`. That much
            // the node's own operator answers.
            //
            // The catalog is the other half, and it is the one this PR is about. A plan numbering a
            // comparison the catalog does not hold is a plan with two answers about what a
            // comparison is: the emitter and the reachability read the numbering, the partition
            // reads the catalog, and each is complete on its own terms while they describe
            // different bodies. Nothing downstream can notice — a partition over an empty catalog
            // draws no line and reports no unread rule, which reads exactly like a model that
            // states none.
            for (Core numbered : byComparison.keySet()) {
                requireIsACatalogued(numbered, comparisons, "numbered");
            }
            for (Core numbered : controlByComparison.keySet()) {
                requireIsACatalogued(numbered, comparisons, "given a control point");
            }
        }

        private static void requireIsACatalogued(Core node, ComparisonCatalog comparisons,
                                                 String what) {
            // Whether it is a comparison at all is asked where that is decided, so this reading
            // holds no list of operators of its own. The two questions stay two: a node that is no
            // comparison and a comparison outside this catalog are different breakages, and one
            // answer for both would send a reader after the wrong one.
            Comparison comparison = node instanceof Core.Binary binary
                    ? Comparison.of(binary).orElse(null) : null;
            if (comparison == null) {
                throw new IllegalArgumentException(
                        "something that is not a comparison was " + what + ": " + node);
            }
            if (comparisons.at(comparison.at()).isEmpty()) {
                throw new IllegalArgumentException("a comparison this plan's catalog does not hold "
                        + "was " + what + " at " + comparison.at().pos()
                        + "; the numbering and the catalog are one answer or they are two");
            }
        }

        public static final Plan NONE = new Plan(List.of(), List.of(), new IdentityHashMap<>(),
                new IdentityHashMap<>(), new IdentityHashMap<>(), new IdentityHashMap<>(),
                java.util.Set.of(), new IdentityHashMap<>(), ComparisonCatalog.of(Map.of()));

        /**
         * Whether one run of the behavior can pass {@code node} more than once.
         *
         * <p>What decides whether a set is enough to say what a run did. A recording holds that a
         * place was passed and not how many times it was, so two facts recorded about a place a run
         * passes twice cannot be told from two facts about one passing — and a statement about
         * several places meeting is about their meeting once, which such a recording cannot answer.
         *
         * <p>Inherited downwards, so a node this is false of stands under nothing this is true of.
         * That is what lets one question asked at a meeting answer for everything the meeting names.
         */
        public boolean mayRepeat(Core node) {
            return mayRepeat.contains(node);
        }

        /**
         * The arms of {@code node}, in the order the emitter emits them, or null where this node has
         * none.
         *
         * <p>Positional and parallel to {@link #probesOf}, and longer in what it can say: every arm
         * is here whether or not a run through it could be recorded. A reader counting what rows are
         * owed wants the probed ones and can ask each; a reader judging what an arm declares wants
         * the arm, which is the one this has and the other does not.
         */
        public ControlPointId.ArmOccurrence[] armsOf(Core node) {
            return armsByNode.get(node);
        }

        /** Which fork {@code node} is, or null where this plan made no arms for it. */
        public ForkOccurrence forkAt(Core node) {
            return forkByNode.get(node);
        }

        /** Which way {@code comparison} coming out {@code result} is, or empty where this plan
         *  numbered no comparison there. */
        public java.util.Optional<ControlPointId.ComparisonPoint> outcomeOf(Core comparison,
                                                                           boolean result) {
            Integer control = controlByComparison.get(comparison);
            return control == null ? java.util.Optional.empty()
                    : comparisonAt(comparison).map(at -> new ControlPointId.ComparisonPoint(
                            control, new ComparisonOutcome(at, result)));
        }

        /**
         * Which comparison of this plan {@code comparison} is, or empty where it numbered none there.
         *
         * <p>What a reading of the model joins on, and what it is given instead of the number. Empty
         * is an ordinary answer for the same reason {@link #comparisonSiteOf} has one.
         */
        public java.util.Optional<ComparisonOccurrence> comparisonAt(Core comparison) {
            Integer site = byComparison.get(comparison);
            return site == null ? java.util.Optional.empty()
                    : java.util.Optional.of(new ComparisonOccurrence(site));
        }

        /**
         * The same, where the caller's own construction says there is one.
         *
         * <p>Absent here is not a comparison that cannot be measured — it is this plan and the reader
         * that found the comparison disagreeing about what a condition is made of, which no
         * measurement should paper over.
         */
        public ComparisonOccurrence requireComparisonAt(Core comparison) {
            return new ComparisonOccurrence(requireComparisonSiteOf(comparison));
        }

        /**
         * Whether this plan numbered any site a run can be recorded at.
         *
         * <p>Not whether it numbered anything. A body whose every arm answers {@code unreachable}
         * has arms, and control points for them, and no site at all — so a reader asking this to
         * find out whether there is anything to be about would skip exactly the bodies a claim is
         * made in.
         */
        public boolean hasNoProbes() {
            return sites.isEmpty();
        }

        /** The probe numbers of {@code node}'s arms, in the order the emitter emits them, or null
         * where this node has none. An entry is {@link #NO_SITE} where that arm answers nothing.
         *
         * <p>Arms only, and positional. A comparison's site is not in here and must not be put in
         * here: the emitter and the readers index this array by an arm's place among its siblings,
         * and anything else in it lights a neighbour's probe. */
        public int[] probesOf(Core node) {
            return byNode.get(node);
        }

        /**
         * Where a comparison's value is recorded, for a comparison that has such a site.
         *
         * <p>Empty is an ordinary answer. What gets a site is decided from the shape of the code —
         * every comparison of a guard's condition — while whether a line is drawn on one is decided
         * later and from more: a comparison the partition reads nothing off keeps its site and nobody
         * asks about it. The emitter walks comparisons in both cases and asks this of each.
         */
        public java.util.OptionalInt comparisonSiteOf(Core comparison) {
            Integer site = byComparison.get(comparison);
            return site == null ? java.util.OptionalInt.empty() : java.util.OptionalInt.of(site);
        }

        /**
         * The same, where the caller's own construction says there is one.
         *
         * <p>A boundary is read off a comparison this plan numbers, so the site was planned before
         * the line was. Absent here is not a boundary that cannot be measured — it is this plan and
         * the reader that found the comparison disagreeing about what a comparison is, which no
         * measurement should paper over.
         */
        public int requireComparisonSiteOf(Core comparison) {
            Integer site = byComparison.get(comparison);
            if (site == null) {
                throw new IllegalStateException(
                        "no comparison site was planned at " + comparison.pos()
                                + "; a line is read off a comparison this plan does not hold");
            }
            return site;
        }

        /** The arms of one behavior, which is what a branch measure counts. */
        public List<Site> arms(String behavior) {
            return sites.stream()
                    .filter(site -> site.behavior().equals(behavior) && site.isArm())
                    .toList();
        }

        public Site site(int index) {
            return sites.get(index);
        }
    }

    /** The sites of every behavior body in one module, numbered in the order the bodies are declared
     * and, within one, in the order the arms are written. */
    public static Plan of(Map<String, Core> behaviorBodies, DecisionSources decisions,
                          SuppliedRules supplied) {
        // Which comparisons there are is not this walk's to decide. Asked here and answered once,
        // so that what gets a number and what a line is drawn on are the same collection read twice
        // rather than two descents that happen to agree.
        ComparisonCatalog comparisons = ComparisonCatalog.of(behaviorBodies);
        Walk walk = new Walk(comparisons, decisions, supplied);
        for (Map.Entry<String, Core> body : behaviorBodies.entrySet()) {
            walk.behavior(body.getKey(), body.getValue());
        }
        return new Plan(List.copyOf(walk.sites), List.copyOf(walk.guards), walk.byNode,
                walk.byComparison, walk.armsByNode, walk.controlByComparison, walk.mayRepeat,
                walk.forkByNode, comparisons);
    }

    private static final class Walk {

        private final List<Site> sites = new ArrayList<>();
        private final List<GuardRef> guards = new ArrayList<>();
        private final IdentityHashMap<Core, int[]> byNode = new IdentityHashMap<>();
        private final IdentityHashMap<Core, Integer> byComparison = new IdentityHashMap<>();
        private final IdentityHashMap<Core, ControlPointId.ArmOccurrence[]> armsByNode =
                new IdentityHashMap<>();
        private final IdentityHashMap<Core, ForkOccurrence> forkByNode = new IdentityHashMap<>();
        private final IdentityHashMap<Core, Integer> controlByComparison = new IdentityHashMap<>();
        /** The reading of the body being walked, which every question about a node in it is asked
         *  of. Rooted at the body because what a name reads is settled by what bound it. */
        private NormalReturn answering = NormalReturn.ofBody(null);
        /** The nodes one run can pass more than once. Kept by identity, like everything else here:
         *  two arms that look the same are equal records and this is about this one. */
        private final java.util.Set<Core> mayRepeat =
                java.util.Collections.newSetFromMap(new IdentityHashMap<>());
        /** Whether the walk is somewhere a run may come back to. Held rather than passed down
         *  because every node below such a place is one, which is what makes it a state of the walk
         *  and not a property of the call. */
        private boolean repeating;
        /** The outcomes that carry nothing of their own. What each of them means is settled with
         *  the construct beside it, so one instance stands for every occurrence. */
        private static final SourceOutcome HELD =
                new SourceOutcome.Held(new SourceOutcome.HeldBy.Condition());
        private static final SourceOutcome FAILED =
                new SourceOutcome.Failed(new SourceOutcome.FailedBy.Condition());
        private static final SourceOutcome BUILT =
                new SourceOutcome.Held(new SourceOutcome.HeldBy.Construction());
        /** Which nodes are comparisons, which this walk asks rather than reads off their shape. */
        private final ComparisonCatalog comparisons;
        private String behavior;
        private int ordinal;
        /** Numbered across the whole plan and never reused, so that one number names one place
         *  whichever behavior it is in — the same rule the probe numbers are under. */
        private int controls;

        private final DecisionSources decisions;
        private final SuppliedRules supplied;

        Walk(ComparisonCatalog comparisons, DecisionSources decisions, SuppliedRules supplied) {
            this.comparisons = comparisons;
            this.decisions = decisions;
            this.supplied = supplied;
        }

        void behavior(String name, Core body) {
            this.behavior = name;
            this.ordinal = 0;
            this.answering = NormalReturn.ofBody(body);
            walk(body, true);
        }

        /**
         * One arm, or {@link #NO_SITE} where no row that stands can be in it.
         *
         * <p>Three things have to hold. The arm has to be able to answer a value; it has to stand
         * somewhere a row can get to — an arm of a {@code match} written after a binding that aborts
         * is a fork nothing reaches, however ordinary the arm itself looks; and the condition above
         * it has to be able to come out its way, since a fork on something the reading settles to one
         * truth sends every run down one arm and leaves the other an arm nothing enters. A row that
         * gets as far as an {@code unreachable} is E1911 and states nothing, so an arm only such a
         * row could go through is an arm no row will ever be recorded in.
         */
        private ControlPointId.ArmOccurrence armOf(SourceOutcome outcome, Core owner,
                                                   CoverageOrigin origin, int part, Core arm,
                                                   boolean reachable,
                                                   DecidedBy decided) {
            // The arm is made either way. Whether a run through it can be recorded is the second
            // question and only the probe turns on it — an arm nothing could record is still an arm,
            // and the readings that judge one need to be able to name it.
            int probe = reachable && answers(arm) && answering.mayEnter(owner, part)
                    ? site(outcome, owner, origin, part, decided) : NO_SITE;
            return new ControlPointId.ArmOccurrence(controls++,
                    probe == NO_SITE ? OptionalInt.empty() : OptionalInt.of(probe),
                    // The fork's own coordinate, as a site takes it: an arm's body is what lowering
                    // rewrites and carries whatever position it was built from, so quoting it sends
                    // an author somewhere else in the file.
                    Citation.of(owner.pos()), origin);
        }

        /**
         * The arms of one fork, and the fork they are arms of.
         *
         * <p>Both written here, in one act. What names the fork is the first of its arms, and it is
         * a name rather than a lookup for exactly that reason: made apart, the fork's identity would
         * be something each reader worked out again from whatever component it had to hand.
         */
        private void arms(Core fork, ControlPointId.ArmOccurrence[] arms) {
            armsByNode.put(fork, arms);
            if (arms.length > 0) {
                forkByNode.put(fork, new ForkOccurrence(arms[0].controlId()));
            }
        }

        /** The probe numbers of {@code arms}, in their order, {@link #NO_SITE} where an arm has
         *  none. What the emitter indexes and what the branch measure counts. */
        private static int[] probesOf(ControlPointId.ArmOccurrence... arms) {
            int[] out = new int[arms.length];
            for (int i = 0; i < arms.length; i++) {
                out[i] = arms[i].probe().orElse(NO_SITE);
            }
            return out;
        }

        /**
         * Whether {@code e} answers a value, asked of the reading of the body it stands in.
         *
         * <p>The walk asks this of every node it passes and of every arm it makes, and the answer is
         * read off the whole subtree — so the reading settles every occurrence in the body once and
         * the walk asks it rather than reading a subtree again per node.
         */
        private boolean answers(Core e) {
            return answering.at(e);
        }

        /**
         * One arm, quoted at the fork it belongs to rather than at its own body.
         *
         * <p>The fork is written by the author and survives lowering; an arm's body is what lowering
         * rewrites, and a rewritten node carries whatever position it was built from — which for a
         * body assembled out of comprehensions and accumulated failures is somewhere else in the file
         * entirely. An arm quoted at a comment sends the author to the wrong place, and there is
         * nothing in the position itself to notice that by.
         *
         * @param owner the {@code if}, {@code match} or attempted construction the arm is one of
         * @param arm   the arm's body, which says what the arm is made of and not where it is
         */
        private int site(SourceOutcome outcome, Core owner, CoverageOrigin origin, int part,
                         DecidedBy decided) {
            // Said here because this is where anything is numbered, and the rule is about numbering
            // rather than about comparisons: an arm of a fork nothing wrote is as much a row nobody
            // can be owed as a comparison of one. Stated for the comparisons alone, it left the arms
            // to be refused further down by whatever noticed first — which was the pair check on
            // `Site`, saying something true about the pair and nothing about the tree.
            if (!origin.isWritten()) {
                throw new IllegalStateException("a construct with no source wrote it is being "
                        + "numbered at " + owner.pos()
                        + "; a tree rebuilt for an analysis is not the tree that runs");
            }
            int index = sites.size();
            // Of the node's own coordinate. This walk is over one module and an arm of a
            // helper another module of this compile wrote is in that module's file, so a
            // source carried here beside the position would be the wrong half of two
            // answers about one place. The walk holds none for that reason.
            sites.add(new Site(behavior, outcome, Citation.of(owner.pos()),
                    index, ordinal++, new Obligation(behavior, origin, part, decided)));
            return index;
        }

        /**
         * Written out rather than reusing {@link Core#forEachChild}: what is being numbered is a
         * {@code Case} and an {@code ElseArm}, which are not {@code Core} and so are not children the
         * generic walk hands over. The switch is exhaustive on purpose — a node added to the IR should
         * stop here and be decided about, not fall silently into a default and go uncounted.
         *
         * <p>Every fork is registered in {@link Plan#byNode} whether or not it is numbered. The
         * emitter generates the bytecode of a body that aborts as it generates any other, and asks
         * this plan for the arms of each fork it meets while doing so; a fork the plan has no entry
         * for stops that generation, which is what makes an omission loud. What a fork nothing
         * reaches has is an entry of {@link #NO_SITE}s — the structure, without the obligation.
         *
         * @param reachable whether a row that stands can get this far. It cannot get past something
         *                  that aborts, so nothing below such a point is a fork a row takes: the row
         *                  that would take it is E1911 and states nothing
         */
        private void walk(Core e, boolean reachable) {
            // Everything below this node is reached by way of the node, so what the node cannot do
            // nothing inside it can do either.
            boolean inside = reachable && answers(e);
            if (repeating) {
                mayRepeat.add(e);
            }
            switch (e) {
                case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                     Core.Read _, Core.UnitValue _, Core.OptionNone _ -> { }
                // A leaf, and one holding no fork. Whether the arm it stands in is an arm to cover is
                // decided where that arm is made, not here.
                case Core.Unreachable _ -> { }
                case Core.Neg n -> walk(n.operand(), inside);
                case Core.FieldAccess fa -> walk(fa.target(), inside);
                case Core.Binary b -> {
                    number(b, inside);
                    walk(b.left(), inside);
                    walk(b.right(), inside);
                }
                case Core.Call c -> c.args().forEach(arg -> walk(arg, inside));
                // What a representation kept standing for an analysis to read. Coverage is measured
                // over the tree that runs, which keeps none of these, so reaching one would mean this
                // count was taken over a tree nothing executes.
                case Core.PreservedCall p -> throw p.unexpectedIn("coverage numbering");
                case Core.Apply a -> a.args().forEach(arg -> walk(arg, inside));
                case Core.LetIn li -> {
                    walk(li.value(), inside);
                    walk(li.body(), inside);
                }
                // A function value, and its arms are arms: what is written here runs when whatever
                // this is handed to applies it, and the rows that make that happen go through them.
                //
                // How many times it applies it is that caller's business and nothing here can say —
                // a comprehension applies one of these per element — so everything inside is a place
                // one run may come back to. Recorded rather than assumed anywhere else: what a set
                // of places can be asked turns on it.
                case Core.Block b -> {
                    boolean outside = repeating;
                    repeating = true;
                    walk(b.body(), inside);
                    repeating = outside;
                }
                case Core.ListLit lit -> lit.elements().forEach(el -> walk(el, inside));
                case Core.OptionSome s -> walk(s.value(), inside);
                case Core.Tuple t -> t.elements().forEach(el -> walk(el, inside));
                case Core.TupleGet tg -> walk(tg.tuple(), inside);
                case Core.Construct nd -> nd.values().forEach(given -> walk(given.value(), inside));
                case Core.If iff -> {
                    walk(iff.cond(), inside);
                    // Which rule this fork decides by, taken before its arms are numbered: two
                    // calls of one library combinator are one fork inlined twice and are not one
                    // thing to cover, and what tells them apart is the rule each was handed.
                    DecidedBy decided =
                            decidedAt(iff.origin(), iff.expansion(), decisions, supplied);
                    ControlPointId.ArmOccurrence then =
                            armOf(HELD, iff, iff.origin(), 0, iff.then(), inside, decided);
                    walk(iff.then(), inside);
                    ControlPointId.ArmOccurrence els =
                            armOf(FAILED, iff, iff.origin(), 1, iff.els(), inside, decided);
                    walk(iff.els(), inside);
                    byNode.put(iff, probesOf(then, els));
                    arms(iff, new ControlPointId.ArmOccurrence[] {then, els});
                    if (then.isMeasured() || els.isMeasured()) {
                        guards.add(new GuardRef(behavior, iff.origin(), decided,
                                then.probe().orElse(NO_SITE), els.probe().orElse(NO_SITE),
                                iff.pos()));
                    }
                }
                case Core.Match m -> {
                    walk(m.scrutinee(), inside);
                    // What a `match` decides by is its subject, as an `if` decides by its condition.
                    // A subject the caller's rule answered is a decision the caller made, and its
                    // arms are one obligation per rule handed in.
                    DecidedBy decided =
                            decidedAt(m.origin(), m.expansion(), decisions, supplied);
                    ControlPointId.ArmOccurrence[] arms =
                            new ControlPointId.ArmOccurrence[m.cases().size()];
                    for (int i = 0; i < m.cases().size(); i++) {
                        Core.Case arm = m.cases().get(i);
                        arms[i] = armOf(matched(arm), m, m.origin(), i, arm.body(), inside,
                                decided);
                        walk(arm.body(), inside);
                    }
                    byNode.put(m, probesOf(arms));
                    arms(m, arms);
                }
                case Core.IfConstructed ic -> {
                    ic.construct().values().forEach(given -> walk(given.value(), inside));
                    // And what an attempted construction decides by is the value it is given.
                    DecidedBy decided =
                            decidedAt(ic.origin(), ic.expansion(), decisions, supplied);
                    ControlPointId.ArmOccurrence[] arms =
                            new ControlPointId.ArmOccurrence[1 + ic.els().size()];
                    arms[0] = armOf(BUILT, ic, ic.origin(), 0, ic.then(), inside, decided);
                    walk(ic.then(), inside);
                    for (int i = 0; i < ic.els().size(); i++) {
                        Core.ElseArm arm = ic.els().get(i);
                        arms[i + 1] = armOf(refused(arm), ic, ic.origin(), i + 1,
                                arm.body(), inside, decided);
                        walk(arm.body(), inside);
                    }
                    byNode.put(ic, probesOf(arms));
                    arms(ic, arms);
                }
            }
        }

        /**
         * One comparison, numbered where a run through it could be recorded.
         *
         * <p>Which nodes are comparisons is {@link ComparisonCatalog}'s answer and not this walk's.
         * Read off the shape of the node here, the numbering came out as the comparisons a fork
         * happened to be written around: a comparison given a name a line above the fork that tests
         * it, or written inside a function value handed to a combinator, is the same construct and
         * got no number, so nothing that joins on one could name it.
         *
         * <p>Deliberately wider than what gets read. Which comparisons a line is drawn on takes the
         * behavior's parameters and the module's symbols to answer, and neither is here — nor should
         * be. A plan's numbering has to be a function of the bodies alone, because the emitter builds
         * one plan and a measurement builds another and the two are the same numbering or the probes
         * mean nothing. A comparison no boundary is drawn on keeps a site nobody asks about, which
         * costs two instructions in a measuring build.
         *
         * @param inside whether a row that stands can get this far and what the comparison stands in
         *               answers a value. A comparison behind an abort is one no run reaches, and a
         *               site for it would be one the emitter lights on no run
         */
        private void number(Core.Binary comparison, boolean inside) {
            // Numbered once. A node reached twice is one comparison written once, and a second number
            // for it would be a site the emitter never lights — which is the shape of a real omission
            // and would be reported as one.
            if (!inside || comparisons.at(comparison).isEmpty()
                    || byComparison.containsKey(comparison)) {
                return;
            }
            // Keyed on where the comparison was written and not on what tests it. A condition can be
            // an application of a function parameter, and then the comparison is the caller's: two
            // predicates written separately are two lines, and one predicate handed to two calls is
            // one, neither of which a fork can say.
            byComparison.put(comparison,
                    site(new SourceOutcome.Compared(comparison.op()), comparison,
                            comparison.origin(), 0, DecidedBy.THE_DECLARATION));
            controlByComparison.put(comparison, controls++);
        }

        private static SourceOutcome matched(Core.Case arm) {
            return new SourceOutcome.Matched(arm.caseTypes());
        }

        private static SourceOutcome refused(Core.ElseArm arm) {
            return new SourceOutcome.Failed(
                    new SourceOutcome.FailedBy.Construction(arm.clause()));
        }
    }

    private CoverageSites() {}
}
