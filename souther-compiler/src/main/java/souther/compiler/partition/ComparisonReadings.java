package souther.compiler.partition;

import souther.compiler.check.ARecursion;
import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.AnalysisBody;
import souther.compiler.check.Choice;
import souther.compiler.check.RecursionOverAList;
import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.BoundOperationFacts;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.diag.Citation;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.SeededWalk;
import souther.compiler.check.StatedComparison;
import souther.compiler.check.Symbols;
import souther.compiler.check.ValueTemplates;
import souther.compiler.core.Core;
import souther.compiler.coverage.Arrivals;
import souther.compiler.types.BinOp;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.Type;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.PathResolution;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhereAnApplicationIsMade;
import souther.compiler.meaning.WrittenLines;
import souther.compiler.types.ValueName;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.OperationLaw;

import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * One reading of a body's comparisons: where each stands, what its names point at, what a row had
 * already satisfied to get there, whether a line may be drawn on it, and what it came to where one
 * may.
 *
 * <p><b>Of the body the analysis reads, which is the tree the language's own operations stand
 * in.</b> A rule written over what such an operation answers is a rule of the model, and the tree
 * the backend emits from has the operation expanded into what it does — so a reading made there
 * met the comparison after the call was gone, while the rules about strings in the same body were
 * read where they stand. Two facts about one position came from two walks of two trees, and a
 * reader wanting both had to know which tree each came from.
 *
 * <p>Which leaves the comparisons inside such an operation out, and that is what it means to leave
 * them out: they are that operation's implementation, and a caller answers for the rules a caller
 * wrote. Where a run through a comparison is recorded is still the emitted tree's, and the two are
 * joined on the construct of the model they agree about
 * ({@link souther.compiler.types.ModelOccurrence}).
 *
 * <p><b>Each comparison is read once, here, and what it came to travels with it.</b> A reader that
 * reports why a comparison bears no line reads the answer off the standing and never reads the
 * arithmetic again: read again downstream, the second reading answers about the form when the
 * question was about where the comparison stands, and a form read to the end is described as one
 * nobody could read.
 *
 * <p><b>One walk, because there is one thing being walked.</b> Three facts about a comparison are
 * settled by where it stands in the body, and each was being worked out by a walk of its own: which
 * names are in force, whether what is computed there is read on the way to an answer, and what the
 * evaluation before it established. Two walks threading the same {@code let} rule through the same
 * tree are two chances to disagree about it, and a fact one of them learned to carry is one the
 * other still drops.
 *
 * <p><b>What stands when a comparison runs is a fact about the position, not about a condition.</b>
 * It was read off {@link Condition}, which is a reading of a subtree and so needs a root — and the
 * root anything ever gave it was a fork's condition. So {@code A && B} established nothing for
 * {@code B} while {@code if A then B else false} did, one model spelled two ways with two answers
 * about where a row for a border on {@code B} is looked for; a name standing for {@code A}
 * established nothing either, because a subtree read on its own has no reading of the names above
 * it. A walk of the body has no root to be given and reaches every position, so what a condition is
 * asked is what it can answer: what a subtree coming out one way establishes
 * ({@link ReachingCuts#stating}), and never where the comparisons are.
 *
 * <p>The two operators are where a walk of the body is not a walk of what runs. {@code &&} and
 * {@code ||} settle as soon as they can, so the right operand runs under what the left one coming
 * out its way established — which is the whole of what makes this per comparison rather than per
 * fork. Everything else evaluates its parts under what stood at it.
 *
 * <p><b>And the case each arm of a {@code match} is, which this tree can name where the tree that
 * runs cannot.</b> A name a closure is handed stands for an element of a container where the
 * operation handing it over still stands, and for no position where that operation is expanded
 * ({@link ArmsNamed}). And which forks a run gets to within one application of each closure around
 * them, which is whether the closures are applied by the operations alone, and how
 * ({@link WithinOneApplication}).
 *
 * @param operationsStanding what this tree says of the forks the tree that runs names less of
 */
record ComparisonReadings(List<Reading> comparisons, List<ForkMet> forks,
                          Map<ConditionOccurrence, Citation> conditionsMet,
                          List<TruthMet> truths, List<ForkDecided> decided,
                          WhereTheOperationsStand operationsStanding) {

    ComparisonReadings {
        comparisons = List.copyOf(comparisons);
        forks = List.copyOf(forks);
        conditionsMet = Map.copyOf(conditionsMet);
        truths = List.copyOf(truths);
        decided = List.copyOf(decided);
    }

    /**
     * A fork's whole condition, as what it coming out each way says and what stood on the way to it.
     *
     * <p>What a run down an arm is seen having done. An arm is taken exactly where the condition
     * came out the arm's way, so what it asks of a row is the whole condition coming out that way —
     * whatever the condition is made of, and whichever of its parts nothing else records.
     *
     * @param fork    the fork, in the tree this walk reads
     * @param assumed every condition on the way to the fork, each with what became of it
     * @param holding what the condition coming out true says
     * @param failing what the condition coming out false says
     */
    record ForkDecided(ConstructOccurrence fork, List<OnTheWay> assumed, List<OnTheWay> holding,
                       List<OnTheWay> failing) {

        ForkDecided {
            assumed = List.copyOf(assumed);
            holding = List.copyOf(holding);
            failing = List.copyOf(failing);
        }
    }

    /**
     * A truth a fork's condition asks, or a part of one asks, and what stood on the way to it.
     *
     * <p>Beside the comparisons because a run is seen coming out of one as it is of a comparison,
     * and a row held to it coming out the other way is composed under what stood on the way to it
     * — which is this walk's to say, and said nowhere else.
     *
     * <p>Only the truths of a fork's condition. Those are the conditions a run is stopped at; a
     * truth that is an answer the body hands back stops nothing.
     *
     * @param assumed every condition on the way to it, each with what became of it
     * @param context where the truth stands: what a construct answering it is in the model is the
     *                copy the call a helper's body was read at makes of it
     */
    record TruthMet(Condition.Truth condition, List<OnTheWay> assumed, CallContext context) {

        TruthMet {
            assumed = List.copyOf(assumed);
        }
    }

    /**
     * A fork the author wrote, the parts of what it tests, and which of them this walk owns.
     *
     * <p>Facts and not a verdict. A fork states a rule of its own only where a part of what it
     * tests is one nothing else answers for, and the readers that could answer are several — a
     * comparison of the values, the position a part is, a predicate over the strings there — so no
     * one of them may settle it. What is here is this walk's half: the parts
     * ({@link ConditionSkeleton}), and the ones this reading claims.
     *
     * <p>Read for every author-written fork and not only the ones that look opaque. A reader
     * joining these with what the other readers found needs the forks they say nothing about as
     * much as the ones they do, and a list already narrowed here would be this walk deciding the
     * question on its own evidence.
     *
     * @param atoms what the fork tests, cut into the parts a rule can be about, each with what of
     *              it this reading does not answer for. Each part carries the reading it is read
     *              in, and the fork carries none of its own: a part is never read where the fork
     *              stands, which is a different place from where a helper or a closure wrote it
     */
    record ForkMet(ConstructOccurrence occurrence, Core condition, Citation at,
                   List<Atom> atoms) {

        ForkMet {
            if (occurrence == null || condition == null || at == null) {
                throw new IllegalArgumentException("a fork of the model is written somewhere");
            }
            atoms = List.copyOf(atoms);
        }

        /**
         * The parts of this fork this reading does not answer for.
         *
         * <p>What the other readers claim is subtracted by whoever holds their answers, which is
         * where the three meet ({@link BehaviorSetStatements}); this says only which parts are left
         * over from what was found here.
         */
        List<Atom> leftHere() {
            return atoms.stream().filter(each -> !each.unanswered().isEmpty()).toList();
        }
    }

    /**
     * One part of what a fork tests, read where what it names stands, and what of what it decides
     * this reading does not answer for ({@link #statedElsewhere}).
     *
     * <p>Worked out once, as the walk meets the fork, and carried to the reader that joins it with
     * the other readers' answers: the walk over what the part turns on is the one that answers
     * both, and walked again there it was the same answer at the same cost a second time.
     *
     * @param unanswered empty where this reading answers for the whole of it: a comparison it read,
     *                   or a position of the input — a fork on such a part tests the values standing
     *                   there and its arms are their classes, so the question is the position's
     */
    record Atom(Denotation at, List<Denotation> unanswered) {

        Atom {
            unanswered = List.copyOf(unanswered);
        }
    }

    /**
     * One comparison of the body, read where it is written.
     *
     * <p>The reading travels with the comparison because it is not the same at every one of them: a
     * comparison inside an expanded helper is about the argument the call handed it, and read
     * against the names outside the binding it is about nothing at all.
     *
     * @param occurrence the construct the author wrote, which is what the rule is identified and
     *                   cited by — a comparison, or an application of an operation the library says
     *                   means one
     * @param statement  what that construct states. Not a node: an emptiness check states its size
     *                   against nought, which no source wrote and which stands nowhere, and an
     *                   application states what the library's law for it says
     * @param assumed    every condition on the way here, each with what became of it. Empty says
     *                   nothing stood on the way, which a comparison at the top of a body is; one
     *                   this reading has no arithmetic for is on the list as a decline, so the two
     *                   are not one answer
     * @param whereEachDecides what each reading of a line of a statement of several asks of a row
     *                   beside the way — one case of where the statement turns on the line — put on
     *                   the way at this comparison; empty where the comparison is one line
     * @param severalStated the comparison as the condition where each of its lines decides is put
     *                   on the way at, which is what any other case of where one decides is put on
     *                   the way at too ({@link #wayToACase}); nothing where it is one line
     * @param metOn      which elements of the input a run makes the comparison on, where it stands
     *                   inside closures an operation stopping at an answer applies to them
     * @param runsAs     the construct as the tree that runs holds it, which is {@code occurrence}
     *                   wherever the body read is the one that runs. A helper's body read at a call
     *                   is not: it runs as the helper's own method, which every call shares, so
     *                   where a run through it is recorded is asked of the construct as that
     *                   method holds it
     * @param context    where it was read: the body the reading was handed, or a helper's body
     *                   read at a call of it
     * @param saidOnTheWay which copies of the model's code put each entry on these ways, told when
     *                   the ways were walked and of these ways alone
     */
    record Reading(ConstructOccurrence occurrence, Stated statement, Citation at,
                   InputReads reads,
                   List<OnTheWay> assumed, BoundaryPolicy.Standing standing,
                   Map<WhereAPartDecides, List<OnTheWay>> whereEachDecides,
                   Optional<Condition> severalStated,
                   ElementsMetOn metOn, ConstructOccurrence runsAs, CallContext context,
                   SaidOnTheWay saidOnTheWay) {

        Reading {
            if (occurrence == null || statement == null || at == null || severalStated == null
                    || metOn == null || runsAs == null || context == null
                    || saidOnTheWay == null) {
                throw new IllegalArgumentException(
                        "a reading is of some comparison of the model, placed somewhere");
            }
            whereEachDecides = Collections.unmodifiableMap(new LinkedHashMap<>(whereEachDecides));
        }

        /**
         * What a row in {@code decides} has met by the time it is at the comparison: the way, and
         * then {@code decides} put on the way where a case of where a line decides is.
         *
         * <p>Any condition over the statement's parts and not only a case one of its readings was
         * read in: a case said for several is asked of each of them, and of what choosing one has
         * chosen so far. The same reading of it as {@link #wayTo} has of a case it holds, read
         * off the same condition, so the two cannot come to say two things of one case.
         *
         * @param read the reading of the input this comparison was read against
         */
        List<OnTheWay> wayToACase(Proposition decides, InputReading read) {
            Condition statedAt = severalStated.orElseThrow(() -> new IllegalArgumentException(
                    "this comparison is one line, and no case of where one decides is put on the"
                            + " way at it: " + decides));
            List<OnTheWay> out = new ArrayList<>(assumed);
            out.addAll(ReachingCuts.whereItDecides(statedAt, decides, read).entries());
            return List.copyOf(out);
        }

        /** What a row at the reading {@code part} of a line has met by the time it is there: the
         *  way, and then the case of where the line decides it is read in. */
        List<OnTheWay> wayTo(WhereAPartDecides part) {
            List<OnTheWay> decides = whereEachDecides.get(part);
            if (decides == null) {
                throw new IllegalArgumentException("this comparison states no " + part);
            }
            List<OnTheWay> out = new ArrayList<>(assumed);
            out.addAll(decides);
            return List.copyOf(out);
        }
    }

    /**
     * What a construct of the model states that lines are drawn on.
     *
     * <p>A comparison, as the checker reads one ({@link BooleanMeaning#asAComparison}); or the
     * truth an application of an operation answers, where that is relations read to the end and
     * one of them is stated by the application and by nothing else written there — {@code
     * List.all} over a closure that never reads its element holds where the container is empty,
     * and no comparison anywhere says so.
     */
    sealed interface Stated {

        /** A comparison, read where the walk meets it. */
        record AComparison(StatedComparison comparison) implements Stated {}

        /**
         * An application, and what it answers comes to on the input: the lines it draws, or the
         * values it relates ({@link Cutting#ofAnApplication}).
         */
        record AnApplication(Core application, Cutting.Read read) implements Stated {}
    }

    /**
     * What some construct of the model states, and that construct.
     *
     * <p>Two facts and not one, because they come apart. A comparison the source wrote is both, and
     * an emptiness check is an application the author wrote stating a comparison they did not: the
     * line is drawn on what is stated, and the rule is the construct that was written.
     */
    private record StatedAt(ConstructOccurrence written, Stated statement) { }


    /**
     * What is the same at every comparison of one body: whose body it is, what the plan numbered,
     * the module's names, the reading of the input, what the input's rules leave each quantity, and
     * what the paths leave arriving at each comparison.
     *
     * <p>Where the reading belongs, and it is not in the environment the walk carries. That
     * environment is a function of the program point — a binding met, an arm entered — and the
     * reading is one value for the whole of this walk. Put in it, the reading would be copied at
     * every step and asked of whichever copy a reader happened to hold.
     */
    private record Body(String behavior, InputReading read,
                        Arrivals answering, Templates templates,
                        List<TruthMet> truths, List<ForkDecided> decided, StatedHere stated,
                        WhatConditionsState conditions, CallContext context, Core root,
                        InputReads atTheRoot, ArmsNamed.Gathered armsNamed,
                        ForkDependencies.Gathered dependencies,
                        WithinOneApplication.Gathered oneApplication) {

        /** The same reading, in the body of a recursive helper read at a call of it: its own
         *  tree, and the copy that call makes of each construct in it. */
        Body inside(Core helperBody, CallContext called, InputReads reads) {
            return new Body(behavior, read, Arrivals.inTheTree(helperBody), templates, truths,
                    decided, stated, conditions, called, helperBody, reads, armsNamed,
                    dependencies, oneApplication);
        }

        /** That the walk met the fork at {@code occurrence} where it is now, as this reading's copy
         *  of it. */
        void forkMet(ConstructOccurrence occurrence) {
            if (occurrence != null) {
                ModelOccurrence.statedAt(context.of(occurrence)).ifPresent(oneApplication::fork);
            }
        }

        Symbols symbols() {
            return read.symbols();
        }

        DeclarationNewtypes newtypes() {
            return read.newtypes();
        }
    }

    /**
     * One reading of {@code body}.
     *
     * <p>Whose body it is is asked for, and it is what a report calls the rules read here. Which
     * comparison of the model each is comes off the node ({@link ModelOccurrence}) and not from the
     * name, so the two cannot come apart: a body read under another's name says the wrong thing in a
     * report and names no other comparison.
     *
     * <p><b>Nothing here is asked about the tree that runs.</b> Where a run through a comparison is
     * recorded, and what a run leaves arriving at its line, are read where the language's operations
     * are expanded — and this reads where they stand. A reading that took either would be one no
     * tree could make on its own.
     */
    static ComparisonReadings of(String behavior, AnalysisBody analysis, InputReading read,
                                 InputReads reads) {
        Core body = analysis.core();
        List<Reading> readings = new ArrayList<>();
        List<ForkMet> forks = new ArrayList<>();
        List<TruthMet> truths = new ArrayList<>();
        List<ForkDecided> decided = new ArrayList<>();
        Templates templates = new Templates(analysis.templates());
        // The names the conditions of this body take, handed out as the walk meets them. One of
        // these per body, because what a name is counted within is the body: counted over the
        // module, an edit to one behavior would rename the conditions of every one after it. Whose
        // reading it is comes off the names it is made against, which is the module being compiled
        // — a condition inside a helper spliced in from elsewhere is still one this reading met.
        ConditionNumbering numbering =
                new ConditionNumbering(read.symbols().module(), behavior,
                        ConditionOccurrence.Reading.DIVIDING);
        StatedHere stated = new StatedHere(behavior);
        WhatConditionsState conditions = WhatConditionsState.of(read);
        // Whether a node answers a value is asked of the tree it stands in: the body, or the
        // template of a value the body builds. A reading that follows a name given a build is in
        // the template from there on, and is answered there — asked of the body instead, a node of
        // the template is one the body was never rooted at.
        List<Core> trees = new ArrayList<>();
        trees.add(body);
        trees.addAll(analysis.templatesAfterTheirBuilders());
        Arrivals answering = Arrivals.inTheTrees(trees, analysis.templates()::bodyOf);
        ArmsNamed.Gathered armsNamed = new ArmsNamed.Gathered();
        ForkDependencies.Gathered dependencies = new ForkDependencies.Gathered();
        WithinOneApplication.Gathered oneApplication = new WithinOneApplication.Gathered();
        walk(body, new Body(behavior, read, answering,
                        templates, truths, decided, stated, conditions,
                        CallContext.OF_THE_BODY, body, reads, armsNamed, dependencies,
                        oneApplication),
                reads, ClosureApplications.OUTSIDE,
                LiveFlow.of(body), List.of(), true, readings, forks, numbering);
        // What each value the body builds states, read once. A value means the same wherever it is
        // built, so what is read of it is one reading however many builds there are; what differs
        // between them is what stood on the way to each, and that is joined into what stood on the
        // way to all of them before the template is read — where a definition is read, which is
        // where a name the body gave a build is read as well.
        InputReads defined = reads.whereValuesAreDefined();
        for (Core template : analysis.templatesAfterTheirBuilders()) {
            Entry entry = templates.joined(template);
            if (entry != null) {
                // No root a way is read from: what stood on the way to a template is every build's
                // way joined, which no walk down the template says.
                walk(template, new Body(behavior, read, answering,
                        templates, truths, decided, stated, conditions,
                        CallContext.OF_THE_BODY, null, null, armsNamed, dependencies,
                        oneApplication),
                        defined, ClosureApplications.OUTSIDE, LiveFlow.of(template),
                        entry.assumed(), entry.live(),
                        readings, forks, numbering);
            }
        }
        return new ComparisonReadings(readings, forks, numbering.metAt(), truths, decided,
                new WhereTheOperationsStand(armsNamed.named(), dependencies.read(),
                        oneApplication.read()));
    }

    /** How one build of a value was reached: what stood on the way to it, and whether what it
     *  computes is read on the way to what the behavior answers with. */
    private record Entry(List<OnTheWay> assumed, boolean live) { }

    /**
     * The builds of values this walk met, by the template each is a build of.
     *
     * <p>Held so that a template is read after every build of it has been, once, under what those
     * builds have in common. Nothing is read at a build: it holds no body, and the body is somewhere
     * every build of it points.
     */
    private static final class Templates {

        private final ValueTemplates held;
        private final Map<Core, List<Entry>> entered = new IdentityHashMap<>();

        Templates(ValueTemplates held) {
            this.held = held;
        }

        Core bodyOf(Core.MaterialisedValue build) {
            return held.bodyOf(build);
        }

        void entered(Core template, List<OnTheWay> assumed, boolean live) {
            entered.computeIfAbsent(template, _ -> new ArrayList<>()).add(new Entry(assumed, live));
        }

        /**
         * What every build of {@code template} stood under, or null where none was met.
         *
         * <p>The conditions every way in agrees on, and a decline from any of them. A row that
         * reaches the template got there by one of the ways, so only what all of them state is
         * owed of every row; anything else would narrow a search past rows that arrive. And a
         * condition that could not be taken in on some way is one the account cannot say it took
         * in, so it stays.
         *
         * <p>A template built once is what that one build stood under, unchanged.
         */
        Entry joined(Core template) {
            List<Entry> ways = entered.get(template);
            if (ways == null) {
                return null;
            }
            boolean live = false;
            List<OnTheWay> common = new ArrayList<>(ways.getFirst().assumed());
            for (Entry way : ways) {
                live |= way.live();
                common.retainAll(way.assumed());
            }
            for (Entry way : ways) {
                for (OnTheWay each : way.assumed()) {
                    if (each instanceof OnTheWay.Declined && !common.contains(each)) {
                        common.add(each);
                    }
                }
            }
            return new Entry(List.copyOf(common), live);
        }
    }

    /**
     * @param applying the applications of the closures this position stands inside, moved by the
     *                 same steps as {@code reads}
     * @param assumed  what evaluating everything before this position established
     * @param live     whether what is computed here is read on the way to what the behavior
     *                 answers with. Carried down because everything inside a value nothing reads is
     *                 read by nothing either
     */
    private static void walk(Core e, Body in, InputReads reads, ClosureApplications applying,
                             LiveFlow flow, List<OnTheWay> assumed, boolean live,
                             List<Reading> out, List<ForkMet> forks,
                             ConditionNumbering numbering) {
        Symbols symbols = in.symbols();
        StatedAt stated = statedAt(e, () -> WhatNamesStandFor.in(reads, in.read()), in.stated());
        if (stated != null) {
            // Which construct of the model it is, off the node. The two readings of a body hold
            // different copies of it and agree about this, so it is what a reader below joins on.
            // Inside a helper's body read at a call, it is the copy that call makes.
            ConstructOccurrence stands = in.context().of(stated.written());
            Citation where = Citation.of(e.pos());
            // Read only where the policy admits it, and under the names in force here, which is
            // the one environment the comparison is about. `answer` is null: a body has nothing
            // that is the answer.
            BoundaryPolicy.Standing standing = BoundaryPolicy.refuses(live)
                    .<BoundaryPolicy.Standing>map(BoundaryPolicy.Standing.Refused::new)
                    .orElseGet(() -> new BoundaryPolicy.Standing.Admitted(
                            switch (stated.statement()) {
                                case Stated.AComparison(var comparison) ->
                                        ComparisonAssessment.of(in.behavior(), comparison, where,
                                                in.read(), reads, applying, null,
                                                in.answering(), false, in.conditions(),
                                                Optional.of(stands.lineage()
                                                        .expansionProjection()));
                                case Stated.AnApplication(var _, var answered) ->
                                        ComparisonAssessment.ofAnApplication(answered, where,
                                                in.read());
                            }));
            Optional<Condition> severalStated = severalStated(e, standing, reads, in, numbering);
            Map<WhereAPartDecides, List<OnTheWay>> decides =
                    whereEachDecides(standing, severalStated, in, numbering);
            List<List<OnTheWay>> ways = new ArrayList<>();
            ways.add(assumed);
            ways.addAll(decides.values());
            out.add(new Reading(stands, stated.statement(), where, reads, assumed, standing,
                    decides, severalStated, applying.elementsMetOn(), stated.written(),
                    in.context(), numbering.saidOnTheWay(ways)));
        }
        // A fork the reading of the runs takes a way out of, under the closures the walk is in. A
        // value standing as a wider type is no fork, and a fork under it is met one step down.
        switch (e) {
            case Core.If iff -> in.forkMet(iff.occurrence());
            case Core.Match match -> in.forkMet(match.occurrence());
            case Core.IfConstructed attempt -> in.forkMet(attempt.occurrence());
            case Core.Binary binary when binary.op().stopsWhenItsAnswerIsSettled() ->
                    in.forkMet(binary.occurrence());
            case Core.Widen _ -> { }
            default -> { }
        }
        switch (e) {
            // The right operand runs only where the left came out the way that leaves the answer
            // unsettled, so what it stands under is what that says. Asked of the operand and not of
            // any fork above it: there need not be one, and where there is, this is what the fork
            // would have been reading anyway.
            //
            // Inside a closure whose applications are said, what the left came to is a statement
            // about each application, so it goes onto what each is reached under and not onto the
            // way every application shares.
            case Core.Binary both when both.op() == BinOp.AND -> {
                walk(both.left(), in, reads, applying, flow, assumed, live, out, forks,
                        numbering);
                walk(both.right(), in, reads, applying.taking(both.left(), true, in.read()), flow,
                        applying.saysWhatStandsInIt() ? assumed
                                : taking(Condition.of(both.left(), reads, symbols, in.newtypes(),
                                        numbering), true, in.read(), assumed, in.conditions(),
                                        numbering),
                        live, out, forks, numbering);
            }
            case Core.Binary either when either.op() == BinOp.OR -> {
                walk(either.left(), in, reads, applying, flow, assumed, live, out, forks,
                        numbering);
                walk(either.right(), in, reads, applying.taking(either.left(), false, in.read()),
                        flow,
                        applying.saysWhatStandsInIt() ? assumed
                                : taking(Condition.of(either.left(), reads, symbols,
                                        in.newtypes(), numbering), false, in.read(), assumed,
                                        in.conditions(), numbering),
                        live, out, forks, numbering);
            }
            // The condition under what stood above the fork, and each arm under what that arm proves
            // of it. A comparison inside a condition is not below the fork: it runs to decide it.
            case Core.If iff -> {
                walk(iff.cond(), in, reads, applying, flow, assumed, live, out, forks, numbering);
                // Read once, whichever arm is being entered. Reaching the `then` and reaching the
                // `els` are two things one condition says, and a second reading for the second arm
                // would name that one condition twice.
                Condition condition =
                        Condition.of(iff.cond(), reads, symbols, in.newtypes(), numbering);
                // What the condition coming out each way says, once: what each arm is entered
                // under, and what a run seen down it is known to have done.
                List<OnTheWay> holding = numbering.said(
                        ReachingCuts.stating(condition, in.read(), true, in.conditions()));
                List<OnTheWay> failing = numbering.said(
                        ReachingCuts.stating(condition, in.read(), false, in.conditions()));
                if (live) {
                    truthsIn(condition, assumed, in.read(), in.truths(), in.conditions(),
                            in.context(), numbering);
                    if (iff.occurrence() != null) {
                        in.decided().add(new ForkDecided(in.context().of(iff.occurrence()),
                                assumed, holding, failing));
                    }
                }
                // What this walk found in the condition, for the reader that decides whether the
                // fork states a rule of its own. Said of every fork an author wrote, and of none
                // this compiler composed — a `guard`'s supplied arm and a lowering's test state
                // nothing about the model.
                //
                // And of none whose answer nothing reads. What is computed where no run reads it
                // divides nothing a row could be held to, which is the same reason a comparison
                // there draws no line ({@link NotABoundary#NOTHING_READS_IT}) — said of the fork
                // too, since a fork is a rule for having been written and a rule nothing reaches
                // is a measure held open over a question no row can answer.
                if (live && iff.occurrence() != null && iff.origin() != null
                        && iff.origin().isWritten()) {
                    // What each part stands for, which is where the readers of it look. The
                    // cutting is of the shape ({@link ConditionSkeleton}) and stops at a name; what
                    // the name denotes is the owner's question, and a reader that could not answer
                    // it would call a fork on a named comparison one nobody read.
                    List<Atom> atoms = new ArrayList<>();
                    for (Denotation part : ConditionSkeleton.atoms(iff.cond(),
                            WhatNamesStandFor.in(reads, in.read()))) {
                        Denotation atom = part.at().denotes(part.value(), symbols, in.newtypes());
                        atoms.add(new Atom(atom, statedElsewhere(atom, in.read(), in.stated())));
                    }
                    forks.add(new ForkMet(in.context().of(iff.occurrence()), iff.cond(),
                            Citation.of(iff.pos()),
                            atoms));
                }
                // And which positions what it turns on may read, under the copy of the fork this
                // reading is of: the one thing the reading of the runs is told of a fork on what an
                // operation over a container answers ({@link ForkDependencies}). Read as the
                // condition's parts were read just above, so a comparison is not read twice.
                if (iff.occurrence() != null) {
                    ModelOccurrence.statedAt(in.context().of(iff.occurrence())).ifPresent(fork ->
                            in.dependencies().forkReads(fork, DemandReading.statedBy(condition,
                                    in.read(), in.conditions())));
                }
                Choice.Decides then = Choice.Decides.ofCondition(iff, true);
                Choice.Decides els = Choice.Decides.ofCondition(iff, false);
                walk(iff.then(), in, reads.choosing(then, symbols, in.newtypes()),
                        applying.taking(iff.cond(), true, in.read())
                                .choosing(then, symbols, in.newtypes(), null),
                        flow, applying.saysWhatStandsInIt() ? assumed : past(assumed, holding),
                        live, out, forks, numbering);
                walk(iff.els(), in, reads.choosing(els, symbols, in.newtypes()),
                        applying.taking(iff.cond(), false, in.read())
                                .choosing(els, symbols, in.newtypes(), null),
                        flow, applying.saysWhatStandsInIt() ? assumed : past(assumed, failing),
                        live, out, forks, numbering);
            }
            // What a `let` computes is read on the way to the answer only where the name is read;
            // everywhere else a value stands in a body it is consumed by what it stands in. And its
            // body is where the name stands for what was bound to it.
            case Core.LetIn let -> {
                // A build of a value is not read here: it holds no body, and what the value states
                // is read once, where the template is. What is recorded is how this build was
                // reached, which is what the template is read under.
                Core given = let.value();
                if (Core.withoutStanding(let.value()) instanceof Core.MaterialisedValue build) {
                    given = in.templates().bodyOf(build);
                    in.templates().entered(given, assumed, live && flow.reads(let));
                } else {
                    walk(let.value(), in, reads, applying, flow, assumed,
                            live && flow.reads(let), out, forks, numbering);
                }
                walk(let.body(), in, reads.and(let.binder(), given),
                        applying.and(let.binder(), given), flow, assumed, live, out, forks,
                        numbering);
            }
            // And each arm under what the arm says the value it matched turned out to be. A name
            // the arm binds is the scrutinee's position narrowed to that case, so a comparison
            // written inside an arm draws its line on a position the reading of the input has —
            // read without it, every rule an author writes inside a `match` was about nothing.
            //
            // The same narrowing is what a row has to be for the arm to be reached at all, so it
            // goes onto the account beside the conditions a guard states. Walked without it, a line
            // inside an arm was owed a row by a walk that had been told nothing stood on the way to
            // it, and the row composed for it was written in whichever arm the values fell in.
            //
            //
            // And the case each arm is, under the copy of the fork this reading is of. Whether a
            // run takes the arm, and whether the reading of the runs named it already, are that
            // reading's to say ({@link ArmsNamed}).
            case Core.Match match -> {
                if (reads.pathOf(match.scrutinee(), in.newtypes())
                        instanceof PathResolution.At(TermPath at)) {
                    List<souther.compiler.reading.Condition.Case> cases = new ArrayList<>();
                    for (Core.Case arm : match.cases()) {
                        cases.add(souther.compiler.reading.Condition.Case.of(at, arm));
                    }
                    ModelOccurrence.statedAt(in.context().of(match.place().occurrence()))
                            .ifPresent(fork -> in.armsNamed().name(fork, cases));
                }
                walk(match.scrutinee(), in, reads, applying, flow, assumed, live, out, forks,
                        numbering);
                for (int part = 0; part < match.cases().size(); part++) {
                    Core.Case arm = match.cases().get(part);
                    Choice.Decides taken = Choice.Decides.ofCase(match, arm);
                    int which = part;
                    walk(arm.body(), in, reads.choosing(taken, symbols, in.newtypes()),
                            applying.choosing(taken, symbols, in.newtypes(), on ->
                                    in.conditions().arm(match, which, on).proposition()), flow,
                            entering(match, arm, part, in.read(), reads, assumed, numbering),
                            live, out, forks, numbering);
                }
            }
            // A walk from a seed is entered as every call is, and its step as every closure is —
            // with each application of the step carrying the seed into the first step, which is
            // what a condition on what the walk carried is read against
            // ({@link ClosureApplications#taking}).
            case Core.PreservedCall call when SeededWalk.of(call, closure ->
                    Core.withoutStanding(reads.standing(closure, symbols, in.newtypes()).value())
                            instanceof Core.Block block ? block : null)
                    instanceof SeededWalk seeded -> ScopeStep.forEachChild(e, (child, step) -> {
                        InputReads inside = reads.entering(step, symbols, in.newtypes());
                        ClosureApplications through =
                                applying.entering(step, symbols, in.newtypes());
                        if (child != seeded.step()) {
                            walk(child, in, inside, through, flow, assumed, live, out, forks,
                                    numbering);
                            return;
                        }
                        Denotation seed = new Denotation(seeded.seed(), reads);
                        in.oneApplication().entering(seeded.step(),
                                shortOfEachElement(seeded.step(), inside, in));
                        ScopeStep.forEachChild(seeded.step(), (body, into) -> walk(body, in,
                                inside.entering(into, symbols, in.newtypes()),
                                through.into(seeded.step(), into, inside, in.read())
                                        .carryingIntoTheFirst(seeded.accumulator(), seed),
                                flow, assumed, live, out, forks, numbering));
                        in.oneApplication().leaving();
                    });
            // A helper that calls itself over a list the input holds, read where the call stands:
            // what its arguments are, and then the arm that takes an element, read at this call
            // with the element standing for any element of the list. Read once, as a closure
            // applied to each element is, and made on an element only where no element before it
            // ended the walk.
            case Core.Call call when recursionAt(call, in, reads, applying)
                    instanceof Recursion over -> {
                ScopeStep.forEachChild(e, (child, step) ->
                        walk(child, in, reads.entering(step, symbols, in.newtypes()),
                                applying.entering(step, symbols, in.newtypes()), flow, assumed,
                                live, out, forks, numbering));
                walk(over.step(), in.inside(over.body(), over.context(), over.reads()),
                        over.reads(),
                        over.applying(), LiveFlow.of(over.body()), assumed, live, out, forks,
                        numbering.within(over.context()));
            }
            // A closure handed the values a container was written with is entered once for all of
            // its applications, each of them carried beside the names as the value it was handed.
            //
            // And what its answer may turn on, read on each application: where an operation's own
            // body forks on what the closure answers, that is what the fork turns on
            // ({@link ForkDependencies}).
            case Core.Block block -> {
                in.oneApplication().entering(block, shortOfEachElement(block, reads, in));
                ScopeStep.forEachChild(block, (child, step) -> {
                    ClosureApplications applied = applying.into(block, step, reads, in.read());
                    if (child == block.body()) {
                        answeredBy(block, applied, in);
                    }
                    walk(child, in, reads.entering(step, symbols, in.newtypes()), applied, flow,
                            assumed, live, out, forks, numbering);
                });
                in.oneApplication().leaving();
            }
            // And each arm of an attempt under what the arm states: the clauses of the invariant it
            // checks, read over what the construction is handed. The built arm is where its name
            // stands for what was built, so a comparison written over that name is one over the
            // positions the construction was given.
            case Core.IfConstructed attempt -> {
                walk(attempt.construct(), in, reads, applying, flow, assumed, live, out, forks,
                        numbering);
                List<Choice.Arm> arms = Choice.of(attempt).arms();
                for (int part = 0; part < arms.size(); part++) {
                    Choice.Arm arm = arms.get(part);
                    int which = part;
                    walk(arm.answers(), in, reads.choosing(arm.decidedBy(), symbols, in.newtypes()),
                            applying.choosing(arm.decidedBy(), symbols, in.newtypes(), on ->
                                    in.conditions().arm(attempt, which, on).proposition()), flow,
                            past(assumed, numbering.said(
                                    ReachingCuts.attempting(attempt, part, arm.answers().pos(),
                                            in.read(), reads, numbering))),
                            live, out, forks, numbering);
                }
            }
            // Every other child under what the step into it binds.
            default -> ScopeStep.forEachChild(e, (child, step) ->
                    walk(child, in, reads.entering(step, symbols, in.newtypes()),
                            applying.entering(step, symbols, in.newtypes()), flow, assumed,
                            live, out, forks, numbering));
        }
    }

    /** The uses of {@code block}, where {@code reads} are the names, that are not an operation
     *  applying it once to each element of a position ({@link WithinOneApplication}). */
    private static List<WhyKept.Shortfall> shortOfEachElement(Core.Block block, InputReads reads,
                                                              Body in) {
        return WithinOneApplication.shortOfEachElement(block, reads, in.read(),
                in.symbols().module(), operation -> asWritten(operation, in.symbols()));
    }

    /** {@code operation} as the author of this module writes it: the sugar, where it is what the
     *  library rewrote one to ({@link souther.compiler.stdlib.Stdlib#writtenAs}). */
    private static String asWritten(ValueName operation, Symbols symbols) {
        return switch (operation) {
            case ValueName.Stdlib.Operation library -> symbols.library().writtenAs(library)
                    .orElse(library).qualified();
            case ValueName.Stdlib library -> library.qualified();
            default -> operation.saidIn(symbols.module());
        };
    }

    /**
     * The body of a helper that calls itself, as one call of it is read.
     *
     * @param body    the helper's body, which is the tree what is in it is answered in
     * @param step    the arm of it that takes an element of the list and goes on
     * @param context the copy this call makes of each construct in it
     * @param reads   the names in force in that arm: the call's arguments for the parameters, and
     *                the element standing for any element of the list
     * @param applying the one application of that arm, made on an element where no element before
     *                it ended the walk
     */
    private record Recursion(Core body, Core step, CallContext context, InputReads reads,
                             ClosureApplications applying) { }

    /**
     * {@code call} read as a call of a helper that walks a list the input holds by its head and
     * calls itself on the rest — or null where it is no such call, or one this reading reads no
     * further.
     *
     * <p>Only outside every closure handed values written out: inside one, each application would
     * hand the call other names, and the walk would be read once per application with nothing
     * yet to say which of them a row's element was met through. Only where the list is a position
     * of the input itself, whose elements are the row's in the row's order. And not where the body
     * builds a value: what a build states is read once, where its template is, and a template read
     * once for every call would be one template read under several calls' names.
     *
     * <p>What ends the walk on an element is every way through the arm to a call of itself
     * failing: the walk goes on past an element exactly where a run through the arm makes one.
     *
     * <p>And only where the way to the call can be read from the body the reading was handed,
     * outside every closure: the helper's method is run by every call of it, so a run recorded
     * there is this call's only where the row met the way to it. Inside a closure the call is made
     * once per application, and which of them a run recorded is nothing a row says.
     */
    private static Recursion recursionAt(Core.Call call, Body in, InputReads reads,
                                         ClosureApplications applying) {
        if (in.root() == null || !in.context().equals(CallContext.OF_THE_BODY)
                || !(applying instanceof ClosureApplications.Outside(var metOn))
                || !(AnOperationApplied.of(call) instanceof AnOperationApplied(
                        ValueName.Helper helper, List<Core> args))) {
            return null;
        }
        ARecursion recursion =
                in.read().rules().declarations().answers().recursionOf(helper).orElse(null);
        RecursionOverAList walk = recursion == null ? null : recursion.walk().orElse(null);
        if (walk == null || buildsAValue(recursion.body().body())
                || !(reads.pathOf(args.get(walk.walked()), in.newtypes())
                        instanceof PathResolution.At(TermPath list))) {
            return null;
        }
        Way made = wayTo(in.root(), call, in.atTheRoot(), in);
        CallContext called = in.context().into(helper, call.occurrence());
        InputReads step = called == null || made == null || made.stated() == null ? null
                : reads.steppingThrough(recursion.body(), args, walk.element().binding(),
                        list.element(), in.newtypes());
        if (step == null) {
            return null;
        }
        List<Proposition> goesOn = new ArrayList<>();
        for (Core.Call again : walk.again()) {
            Way way = wayTo(walk.some().body(), again, step, in);
            if (way != null && way.stated() == null) {
                return null;
            }
            if (way != null) {
                goesOn.add(way.stated());
            }
        }
        Proposition onward = WhereAnApplicationIsMade.alongOneOf(goesOn);
        return new Recursion(recursion.body().body(), walk.some().body(), called, step,
                new ClosureApplications.Each(List.of(new ClosureApplications.Application(step,
                        WhereAnApplicationIsMade.nothingAsked(), Map.of(),
                        metOn.madeWhere(made.stated()).stoppingIn(list, onward.denied())))));
    }

    /**
     * The way to somewhere in a tree: what a run has to meet to get there, or nothing where that is
     * not read — a closure stands on the way, applied wherever whatever it is handed to applies it,
     * or a fork whose arms no reading here states.
     */
    private record Way(Proposition stated) {

        static final Way NOT_READ = new Way(null);

        /** This way, past {@code entered} on the way into it. */
        Way past(Proposition entered) {
            return stated == null || entered == null ? NOT_READ
                    : new Way(WhereAnApplicationIsMade.past(entered, stated));
        }
    }

    /**
     * The way a run of {@code e} under {@code reads} takes to {@code target}, or null where
     * {@code e} does not hold it.
     *
     * <p>Each fork on the way asks the arm it is entered by, and an operator stopping at an answer
     * asks its left side to leave the answer open.
     */
    private static Way wayTo(Core e, Core target, InputReads reads, Body in) {
        if (e == target) {
            return new Way(WhereAnApplicationIsMade.nothingAsked());
        }
        if (e instanceof Core.Binary both
                && (both.op() == BinOp.AND || both.op() == BinOp.OR)) {
            Way left = wayTo(both.left(), target, reads, in);
            if (left != null) {
                return left;
            }
            Way right = wayTo(both.right(), target, reads, in);
            if (right == null) {
                return null;
            }
            Proposition leftAnswered =
                    in.conditions().truth(both.left(), reads, in.read()).proposition();
            return right.past(both.op() == BinOp.AND ? leftAnswered : leftAnswered.denied());
        }
        if (e instanceof Core.Block) {
            return holds(e, target) ? Way.NOT_READ : null;
        }
        Way[] found = {null};
        ScopeStep.forEachChild(e, (child, step) -> {
            if (found[0] != null) {
                return;
            }
            Way inside = wayTo(child, target,
                    reads.entering(step, in.symbols(), in.newtypes()), in);
            if (inside != null) {
                found[0] = inside.past(step instanceof ScopeStep.Chosen
                        ? enteredBy(e, child, reads, in)
                        : WhereAnApplicationIsMade.nothingAsked());
            }
        });
        return found[0];
    }

    /**
     * What a run entering {@code arm}, an arm of {@code fork}, meets: the condition coming out
     * that arm's way, or what taking the arm states — or null for an arm of a fork no reading here
     * states the arms of.
     */
    private static Proposition enteredBy(Core fork, Core arm, InputReads reads, Body in) {
        if (fork instanceof Core.If iff) {
            Proposition holds = in.conditions().truth(iff.cond(), reads, in.read()).proposition();
            return arm == iff.then() ? holds : holds.denied();
        }
        if (fork instanceof Core.Match || fork instanceof Core.IfConstructed) {
            List<Choice.Arm> arms = Choice.of(fork).arms();
            for (int part = 0; part < arms.size(); part++) {
                if (arms.get(part).answers() == arm) {
                    return in.conditions().arm(fork, part, reads).proposition();
                }
            }
        }
        return null;
    }

    /** Whether {@code target} stands in {@code e}. */
    private static boolean holds(Core e, Core target) {
        if (e == target) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || holds(child, target));
        return found[0];
    }

    /** Whether {@code e} builds a value anywhere in it. */
    private static boolean buildsAValue(Core e) {
        if (e instanceof Core.MaterialisedValue) {
            return true;
        }
        boolean[] found = {false};
        Core.forEachChild(e, child -> found[0] = found[0] || buildsAValue(child));
        return found[0];
    }

    /**
     * Every truth {@code condition} asks, each with what stood on the way to it: what stood before
     * the condition, and for a part after a connective, what the parts before it coming out the
     * way that runs it say.
     */
    private static void truthsIn(Condition condition, List<OnTheWay> assumed, InputReading read,
                                 List<TruthMet> out, WhatConditionsState conditions,
                                 CallContext context, ConditionNumbering numbering) {
        switch (condition) {
            case Condition.Truth truth -> out.add(new TruthMet(truth, assumed, context));
            case Condition.Compares _ -> { }
            // The right part runs where the left leaves the answer open, which under a conjunction
            // is the left holding and under a disjunction the left failing.
            case Condition.Joined joined -> {
                truthsIn(joined.left(), assumed, read, out, conditions, context, numbering);
                boolean leftHolding = joined.how().under(true) == ConditionJoin.BOTH;
                truthsIn(joined.right(),
                        taking(joined.left(), leftHolding, read, assumed, conditions, numbering),
                        read, out, conditions, context, numbering);
            }
        }
    }

    /**
     * What each reading of each line of the statement {@code e} makes asks of a row for the
     * statement to turn on it, put on the way at {@code e} — or nothing, where the comparison is
     * one line or draws none.
     */
    private static Map<WhereAPartDecides, List<OnTheWay>> whereEachDecides(
            BoundaryPolicy.Standing standing, Optional<Condition> statedAt, Body in,
            ConditionNumbering numbering) {
        if (!(standing instanceof BoundaryPolicy.Standing.Admitted admitted)
                || !(admitted.read() instanceof ComparisonAssessment.Several several)
                || statedAt.isEmpty()) {
            return Map.of();
        }
        Condition at = statedAt.get();
        Map<WhereAPartDecides, List<OnTheWay>> out = new LinkedHashMap<>();
        for (ComparisonAssessment.Several.Part part : several.parts()) {
            for (WhereAPartDecides reading : part.readings()) {
                out.put(reading, numbering.said(
                        ReachingCuts.whereItDecides(at, reading.decides(), in.read())));
            }
        }
        return out;
    }

    /**
     * The comparison {@code e} as a condition, where its statement is several lines: what where
     * each of them decides is put on the way at — nothing where it is one line or draws none.
     */
    private static Optional<Condition> severalStated(Core e, BoundaryPolicy.Standing standing,
                                                     InputReads reads, Body in,
                                                     ConditionNumbering numbering) {
        return standing instanceof BoundaryPolicy.Standing.Admitted admitted
                && admitted.read() instanceof ComparisonAssessment.Several
                ? Optional.of(Condition.of(e, reads, in.symbols(), in.newtypes(), numbering))
                : Optional.empty();
    }

    /**
     * What stands past {@code node} coming out {@code holding}: what stood before it, and what that
     * says.
     *
     * <p>Asked of {@link ReachingCuts#stating}, which is the same rule that says what reaching an
     * arm of a fork establishes. Both are "this subtree came out this way, so what follows", and
     * written apart they would agree by having been derived alike — until one of them learned to
     * read a shape of condition the other did not.
     */
    private static List<OnTheWay> taking(Condition condition, boolean holding,
                                         souther.compiler.inputs.InputReading read,
                                         List<OnTheWay> assumed, WhatConditionsState conditions,
                                         ConditionNumbering numbering) {
        return past(assumed, numbering.said(
                ReachingCuts.stating(condition, read, holding, conditions)));
    }

    /** What stood before, and then what was {@code stated} past it. */
    private static List<OnTheWay> past(List<OnTheWay> assumed, List<OnTheWay> stated) {
        List<OnTheWay> out = new ArrayList<>(assumed);
        out.addAll(stated);
        return List.copyOf(out);
    }

    /** The same, for what standing inside one arm of a fork establishes ({@link
     *  ReachingCuts#entering}). */
    private static List<OnTheWay> entering(Core.Match match, Core.Case arm, int part,
                                           InputReading read, InputReads reads,
                                           List<OnTheWay> assumed, ConditionNumbering numbering) {
        return past(assumed, numbering.said(
                ReachingCuts.entering(match, arm, part, read, reads, numbering)));
    }

    /**
     * What {@code e} states and the construct it is written as, or null where it states nothing
     * lines are drawn on.
     *
     * <p>What a construct means is the checker's answer ({@link BooleanMeaning#asAComparison}),
     * asked once: a comparison states itself, and an operation the library says means a size
     * against nought states that. Only of a construct an author wrote — one this compiler composed
     * states no rule of the model, which is what an unwritten construct says of itself.
     *
     * <p>Asked of the node as it stands and not through what it stands as, so a comparison held as
     * another type is met once, where it is, and not again at its wrapper.
     *
     * <p>And none where what it states is carried past it to the input ({@link
     * Pullback#carriesPast}): the rules there are the ones it was carried to, and the fork around it
     * is what turns on them. The names are asked for only there: this is asked at every node a
     * walk meets, and nearly all of them are no construct that states one.
     *
     * <p>An application answering a truth that is no comparison states the lines its law draws
     * where one of them is its own ({@link StatedHere#ofAnApplication}).
     */
    private static StatedAt statedAt(Core e, Supplier<WhatNamesStandFor> names,
                                     StatedHere here) {
        ConstructOccurrence written = switch (e) {
            case Core.Binary binary -> binary.occurrence();
            case Core.PreservedCall call -> call.occurrence();
            default -> null;
        };
        if (written == null || !written.isWritten()) {
            return null;
        }
        Optional<StatedComparison> compared = BooleanMeaning.asAComparison(e);
        if (compared.isPresent()) {
            return here.carriesPast(e, compared.get(), names) ? null
                    : new StatedAt(written, new Stated.AComparison(compared.get()));
        }
        Cutting.Read answered = e instanceof Core.PreservedCall call
                && (Type.BOOL.equals(call.type()) || statesWhetherItHoldsAValue(call))
                ? here.ofAnApplication(call, names) : null;
        return answered == null ? null
                : new StatedAt(written, new Stated.AnApplication(e, answered));
    }

    /**
     * Whether the library says by a law when {@code call} answers a value rather than nothing,
     * which is what an operation answering an optional states of the input.
     *
     * <p>Asked of the operation's facts and not of the type of what it answers: an optional is
     * what holds a value or none, and which operations say when are the library's to declare.
     */
    private static boolean statesWhetherItHoldsAValue(Core.PreservedCall call) {
        return DefaultBoundOperationFacts.get().settled(call.operation(),
                OperationLaw.Observed.PRESENCE) instanceof BoundOperationFacts.Settled.ByALaw;
    }

    /**
     * What the constructs one reading of a body meets state, asked once per construct and
     * reading of its names.
     *
     * <p>A construct is met where the walk reaches it and again as a part of each fork that turns
     * on it, and the answer is a reading of what it states. Read under names that are the same
     * value, it is the same reading; so it is kept, and the walk and every fork are answered by it.
     */
    private static final class StatedHere {

        /** A construct, by the node it is, under a reading of its names, by what that holds. */
        private record Asked(Core node, InputReads reads) {

            @Override
            public boolean equals(Object other) {
                return other instanceof Asked that && node == that.node && reads.equals(that.reads);
            }

            @Override
            public int hashCode() {
                return System.identityHashCode(node) * 31 + reads.hashCode();
            }
        }

        private final String behavior;
        private final Map<Asked, Boolean> carried = new HashMap<>();
        private final Map<Asked, Optional<Cutting.Read>> applications = new HashMap<>();

        StatedHere(String behavior) {
            this.behavior = behavior;
        }

        /** Whether what a comparison states is carried past it ({@link Pullback#carriesPast}). */
        boolean carriesPast(Core e, StatedComparison statement,
                            Supplier<WhatNamesStandFor> names) {
            if (!Pullback.mayBeCarriedPast(statement)) {
                return false;
            }
            WhatNamesStandFor standing = names.get();
            return carried.computeIfAbsent(new Asked(e, standing.reads()),
                    _ -> Pullback.carriesPast(statement, e, standing.reads(), standing.read()));
        }

        /**
         * What the truth {@code application} answers comes to on the input, or null where it
         * states nothing of its own.
         *
         * <p>Its own where a part of what it states was read off the application itself: a part
         * read off a comparison inside it, or off a position, is that comparison's or that
         * position's, and a statement made only of those is theirs. And only a statement read to
         * the end that is lines on the input or values it relates
         * ({@link Cutting#ofAnApplication}): anything short of that is a fork's to say, at the
         * positions it came from.
         */
        Cutting.Read ofAnApplication(Core.PreservedCall application,
                                     Supplier<WhatNamesStandFor> names) {
            WhatNamesStandFor standing = names.get();
            return applications.computeIfAbsent(new Asked(application, standing.reads()), _ -> {
                // Whether an optional holds a value is what it states, as a truth is what it
                // answers.
                WhatConditionsState state = WhatConditionsState.of(standing.read());
                Pullback.Pulled stated = Type.BOOL.equals(application.type())
                        ? state.truth(application, standing.reads(), standing.read())
                        : state.presence(application, standing.reads(), standing.read());
                boolean itsOwn = stated.turnsOn().stream().anyMatch(leaf ->
                        Core.withoutStanding(leaf.from().value()) == application);
                if (!itsOwn || Proposition.leavesSomethingUnread(stated.proposition())) {
                    return Optional.empty();
                }
                return Optional.ofNullable(Cutting.ofAnApplication(behavior, application,
                        stated.proposition(), standing.read(), standing.reads(),
                        WrittenLines.of(stated.meaning().how(),
                                application.occurrence().lineage().expansionProjection(),
                                Optional.empty(), Optional.empty())));
            }).orElse(null);
        }
    }


    /**
     * What the answer of {@code block}, applied as {@code applied} says, may turn on, filed under
     * the construct it answers with: where an operation's own body forks on what the closure
     * answers, that construct is what decides the fork ({@link ForkDependencies}).
     *
     * <p>Read on every application, since each is handed a value of its own. A closure no run
     * applies decides nothing, and one whose applications are not said may turn on anything. Only
     * a closure answering a truth decides an operation's fork by what it answers, so one answering
     * anything else is read as nothing here, which is what a fork finding no entry makes of it.
     */
    private static void answeredBy(Core.Block block, ClosureApplications applied, Body in) {
        if (!Type.BOOL.equals(block.body().type())) {
            return;
        }
        Optional<ModelOccurrence> answers = souther.compiler.reading.Condition.Arm
                .decidingConstructOf(block.body())
                .flatMap(at -> ModelOccurrence.statedAt(in.context().of(at)));
        if (answers.isEmpty()) {
            return;
        }
        switch (applied) {
            case ClosureApplications.Each(var each) -> each.forEach(one ->
                    in.dependencies().answerReads(answers.get(), in.conditions()
                            .truth(block.body(), one.reads(), in.read()).proposition()));
            case ClosureApplications.None _ -> { }
            case ClosureApplications.Outside _, ClosureApplications.NotSaid _ ->
                    in.dependencies().answerUnbounded(answers.get());
        }
    }

    /**
     * Whether something other than the fork itself states what {@code atom} decides.
     *
     * <p>Three readers could own it and each of them is asked the same way: a comparison of the
     * model, a position of the input the part is the value at, and another fork the source wrote.
     * Asked of the part rather than of the condition — a fork testing two things owns one of them
     * and leaves the other, and an answer about the whole would lose that.
     *
     * <p><b>Along what the part's answer turns on, for every one of them.</b> A rule written in a
     * closure one of the language's operations is handed reaches the fork where the library says
     * the answer turns on what that closure said ({@link WhatAForkTests}) — a filter answers fewer
     * for exactly that reason and a mapping does not, and the two calls are the same shape. Which
     * is a fact about the operation and not about the kind of rule on the other side of it: asked
     * along the edge for a comparison and at the part itself for a position,
     * {@code List.any(x -> x > 0, xs)} states nothing of its own while
     * {@code List.any(p -> p.active, xs)} states a rule nobody wrote.
     *
     * <p><b>Two of the three and not the third.</b> A fork the answer turns on may state a rule of
     * its own, and whether it does is not a fact about the fork's shape: a condition nobody else
     * answers for and that is about no position of the input states nothing, so a source-written
     * fork there is no rule for an outer one to be owned by. Read as one, a fork over such a
     * closure would be owned by a rule that does not exist and the question it leaves would go with
     * it. So that owner is asked where the rules themselves are known
     * ({@code BehaviorSetStatements#ofTheirOwn}), of the rules and not of the source.
     *
     * <p><b>Answered as the parts nobody else states, and not as whether somebody states one.</b>
     * What an operation's answer turns on is as many things as the closure states
     * ({@link WhatAForkTests#partsOfTheAnswer}): a closure answering
     * {@code p.age > 18 && List.contains(0, p.tags)} states a comparison and something nothing here
     * reads, and the fork around the operation states the second whoever owns the first. Answered
     * as "something in there is owned", the second went with the first — which is the same partial
     * ownership a condition's own parts are cut along, lost one step past the operation.
     *
     * <p><b>None, where the part is a construct that states what it decides, read to the
     * end.</b> Every relation its statement holds is one of its lines, whichever node it was read
     * off: {@code List.length(List.take(n, xs)) >= 1} holds where {@code n} is at least one and
     * {@code xs} holds something, and the comparison draws both. A statement with a part nobody
     * read leaves that part where it was read off, as any other part is.
     */
    private static List<Denotation> statedElsewhere(Denotation atom, InputReading read,
                                                    StatedHere here) {
        StatedAt whole = statedAt(atom.value(), () -> WhatNamesStandFor.in(atom.at(), read), here);
        if (whole != null && switch (whole.statement()) {
            case Stated.AnApplication _ -> true;
            case Stated.AComparison(var comparison) -> !Proposition.leavesSomethingUnread(
                    WhatConditionsState.of(read).comparison(comparison, atom.at(), read)
                            .stated().proposition());
        }) {
            return List.of();
        }
        List<Denotation> left = new ArrayList<>();
        for (Denotation part : WhatAForkTests.partsOfTheAnswer(atom.value(),
                WhatNamesStandFor.in(atom.at(), read))) {
            // Which rule the part is, by the node; where it stands, in the reading it is written in.
            if (statedAt(part.value(), () -> WhatNamesStandFor.in(part.at(), read), here) == null
                    && !(part.at().pathOf(part.value(), read.rules().newtypes())
                            instanceof PathResolution.At)) {
                left.add(part);
            }
        }
        return left;
    }

    /** The parts of what {@code atom} decides that none of the three readers answers for, which is
     *  what a fork over it is left stating. */
    static List<Denotation> leftUnread(Atom atom, PredicateReadings predicates) {
        return atom.unanswered().stream()
                .filter(part -> !predicates.statesOneAt(part.value()))
                .toList();
    }
}
