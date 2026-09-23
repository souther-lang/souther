package souther.compiler.partition;

import souther.compiler.coverage.ArmProbe;
import souther.compiler.observe.Classification;
import souther.compiler.reading.CoverageRead;
import souther.compiler.reading.Interaction;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Ways a test with no measurement beside it stands a generation up on its own.
 *
 * <p>None of these is what a build asks for — {@link Generator#fill(GenerationPlan, List,
 * Generator.CandidateCheck, CoverageRead.Read, Generator.Trial, List, AnswersStoodIn,
 * AdequacyPolicy.OfTheGeneration)} is, and it is the only form main ever calls. What is owed a row
 * is {@code Adequacy.RowsOwed}'s answer there, read off the measure and not off the written rows a
 * second time. A test standing the search up in isolation has no such measure to read, so it needs
 * a way to name obligations of its own — which is what these are for, and why they read the rows
 * or the groups handed to them directly rather than reaching for {@code Adequacy.RowsOwed}.
 */
final class GenerationFixtures {

    /**
     * Rows for every class of the behavior's positions no written row sits in.
     *
     * <p>Deterministic: the axes are ordered before anything starts, ties go to the lower index, and
     * nothing consults a clock or a hash order — the same model and the same rows produce the same
     * rows twice. Nothing is asked about the body here, so no arm is looked for.
     */
    static FillResult fill(MeasuredInput subject, List<Generator.ObservedRow> existing,
                           Generator.CandidateCheck check,
                           AdequacyPolicy.OfTheGeneration budget) {
        return fill(subject, existing, check,
                new CoverageRead.Read(List.of(), new LinkedHashMap<>()), budget);
    }

    /**
     * The same, and a row through every arm the body has.
     *
     * <p>Two questions and one set of rows. A class is what the model divides a position into and is
     * answerable with no body to read; an arm is a place in the body, and where a row through it is
     * looked for is what the reading says it takes to arrive there. The classes go first: what each
     * is owed is one row, and a budget the arms spent first left a class the report names with
     * nothing offered for it.
     */
    static FillResult fill(MeasuredInput subject, List<Generator.ObservedRow> existing,
                           Generator.CandidateCheck check, CoverageRead.Read read,
                           AdequacyPolicy.OfTheGeneration budget) {
        return fill(subject, existing, check, read, Generator.Trial.NOTHING_RUNS, budget);
    }

    /**
     * The same, running each row composed at a combination to see whether it took the arm.
     *
     * <p>Which is the only thing that can say so. A row is composed by narrowing each position to
     * the classes the combination leaves it, and every step of that narrowing is a reading of the
     * body — so a row that misses is what a reading being wrong looks like, and a row that misses
     * looks like one that arrives until something watches it.
     *
     * <p>A row that missed is not offered and the arm stays unanswered. It is not evidence that the
     * arm is unreachable: what was shown is that these candidates were not witnesses (ADR-0091).
     *
     * <p>For a behavior that requires nothing. What a row stands its target's dependencies in with
     * is the plan-taking search's parameter, and a caller whose behavior requires one has to say
     * what it answers rather than reach a search that composes rows nothing can apply.
     */
    static FillResult fill(MeasuredInput subject, List<Generator.ObservedRow> existing,
                           Generator.CandidateCheck check, CoverageRead.Read read,
                           Generator.Trial trial, AdequacyPolicy.OfTheGeneration budget) {
        // Both in the order their own walks reached them: the positions the search fixes them in,
        // and the numbers the plan gave the arms. Each is what that walk means by its order.
        return Generator.fill(planOver(subject, everyClassNoRowSitsIn(subject, existing),
                        List.copyOf(read.arms().keySet())),
                existing, check, read, trial, List.of(), AnswersStoodIn.REQUIRING_NOTHING,
                budget);
    }

    /**
     * The same, for a caller that gathered its obligations itself.
     *
     * <p>A test standing the search up on its own is the caller this is for. The plan is still what
     * the search is asked with — there is no way in that does not carry one — and this is where the
     * one such a caller holds is assembled.
     */
    static FillResult fill(MeasuredInput subject, List<Generator.ObservedRow> existing,
                           Generator.CandidateCheck check, CoverageRead.Read read,
                           Generator.Trial trial, List<Generator.Baseline> baselines,
                           List<ClassOfAPosition> classesOwed, List<ArmProbe> armsOwed,
                           AdequacyPolicy.OfTheGeneration budget) {
        return Generator.fill(planOver(subject, classesOwed, armsOwed), existing, check, read,
                trial, baselines, AnswersStoodIn.REQUIRING_NOTHING, budget);
    }

    /**
     * A plan over what a caller gathered, in the order they gathered it.
     *
     * <p>Ordered, because the plan is. Which order it is belongs to whoever gathered the
     * obligations: a walk that gathers each thing once knows what its own order means, and a set
     * handed over here would leave that to whatever collection the caller happened to hold — so
     * this takes the answer rather than the collection it was kept in.
     */
    static GenerationPlan planOver(MeasuredInput subject, List<ClassOfAPosition> classes,
                                   List<ArmProbe> arms) {
        return GenerationPlan.of(subject, classes,
                arms.stream().map(Generator.ArmOwed::new).toList(), List.of(), List.of());
    }

    /**
     * Every arm a combination of the body may take, which is at least every arm one does take.
     *
     * <p><b>Not what a build asks for.</b> Which arms are owed a row is what measuring them
     * established, and a build hands that in. This is for a caller with no measurement beside it —
     * a test standing the search up on its own — and it says so by being a list the caller passes
     * rather than one the search makes for itself.
     *
     * <p><b>And <em>may</em> rather than <em>does</em>, which the name carries because the answer
     * cannot.</b> An offered group is walked, so what it contributes is exact: a choice whose
     * factors leave a position nothing is not a combination and is not counted. A group the budget
     * held back is not walked, and what it contributes is the union over the way in and every
     * outcome of every factor — which includes arms no single combination of it claims, since two
     * factors that disagree about a position have choices no row sits in.
     *
     * <p>That direction is the safe one and the other is not. An arm left out of what a caller asks
     * for is an arm this composes nothing for, and a caller with no measurement beside it has
     * nothing to tell that from an arm nothing could be composed for. An arm asked for and not
     * found says what each place it was looked in came to.
     */
    static Set<ArmProbe> everyArmACombinationMayTake(
            MeasuredInput subject, List<Interaction> groups,
            AdequacyPolicy.OfTheGeneration budget) {
        Set<ArmProbe> out = new LinkedHashSet<>();
        InteractionCells.Offered offered =
                InteractionCells.of(groups, Generator.ordered(subject).axes(), budget.cellsPerGroup());
        for (InteractionCells.Group group : offered.groups()) {
            for (int index = 0; index < group.size(); index++) {
                CellSelection selection = group.at(index);
                if (selection != null) {
                    out.addAll(Generator.claimed(selection));
                }
            }
        }
        // And the arms behind a group the limit held back. They are arms the combinations take —
        // what the limit settled is that nothing walked them, which is the search's answer and not
        // a fact about which arms exist. Left out, a caller with no measurement beside it asks for
        // fewer arms because this compiler declined to look, and never learns that it did.
        for (InteractionCells.NotOffered held : offered.notOffered()) {
            out.addAll(Generator.armsIn(held.claims()));
        }
        return out;
    }

    /**
     * Every class of every position no row the author wrote sits in.
     *
     * <p><b>Not what a build asks for, and not {@code Adequacy.RowsOwed}'s answer either.</b> Which
     * classes are owed a row is what the partition measure established, and a build hands that in.
     * This reads the written rows a second time instead, which is right only for a caller with no
     * measure beside it to read — a test standing the search up on its own — and it says so by being
     * a list the caller passes rather than one the search makes for itself.
     *
     * <p>Read off the values the rows state, which needs nothing run: where a row stands is settled
     * by what is written at each position. So the answer is the same one the measure reaches, and a
     * build that ran nothing is not a build with nothing to generate for.
     *
     * <p>A row of the author's can sit in more than one class of a position at once — a list with
     * one element under a line and one over it — and each of them is covered. Read as one class,
     * the rest would be asked for again, which is work the author has already done.
     */
    static List<ClassOfAPosition> everyClassNoRowSitsIn(MeasuredInput subject,
                                                        List<Generator.ObservedRow> existing) {
        // Gathered once apiece and handed over in the order the walk reached them, which is the
        // order the search fixes the positions in. The set is how "once apiece" is kept; what a
        // caller is given is the order, because that is what the plan is asking for.
        Set<ClassOfAPosition> out = new LinkedHashSet<>();
        for (Axis axis : Generator.ordered(subject).axes()) {
            Set<String> covered = new LinkedHashSet<>();
            for (Generator.ObservedRow row : existing) {
                Classification here = row.at().get(axis.id());
                if (here != null) {
                    covered.addAll(here.classIds());
                }
            }
            for (PartitionClass cls : axis.classes()) {
                if (!covered.contains(cls.id())) {
                    out.add(new ClassOfAPosition(axis.id(), cls.id()));
                }
            }
        }
        return List.copyOf(out);
    }

    private GenerationFixtures() {}
}
