package souther.compiler.query;

import souther.compiler.check.FakeTables;
import souther.compiler.examples.ExampleProvisioning;
import souther.compiler.examples.ExampleStatements;
import souther.compiler.partition.AnAnswerComposed;
import souther.compiler.partition.AnswerDemand;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.AnswersStoodIn;
import souther.compiler.partition.CompositionAccount;
import souther.compiler.partition.DemandGap;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.InjectedAnswer;
import souther.compiler.partition.StandInAttempt;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

/**
 * What a row takes to stand a behavior's dependencies in for one way through its body.
 *
 * <p>Every dependency the behavior requires, and not only the ones the way turns on. A row that
 * answers what the way asks and leaves a clock unanswered is a row nothing applies, so the two are
 * composed together — the first against what the way demands, the rest against what their own
 * answer type leaves.
 *
 * <p><b>One value per dependency, which is what a row writes as a {@code with}.</b> A way that
 * needs one to answer differently at different calls needs a table, and a table is written once for
 * a module — it belongs to the environment several rows share rather than to a row. Nothing here
 * composes one.
 *
 * <p><b>What the module already states is that environment, and a row is composed inside it.</b> A
 * dependency the module writes a {@code fake} for is answered by that table, and the row writes at
 * it only what it has to say of its own — which is where the way turns on what the dependency
 * answers and a value serving every call composes. So a way that wants a table is a way this
 * compiler has a row for wherever the module states one, and a way that wants nothing of a
 * dependency the module answers leaves it answered rather than writing over it: a row of a module
 * runs in the environment the module's written rows run in, or what a search certified is not what
 * an author pastes.
 *
 * <p>Whether the table answers what the way needs is the run's to settle and is not decided here.
 * Reading the table to find out would be a second answer to which of its rows answers a call, and
 * it would be a reading — which is the thing a trial exists because it may be wrong.
 *
 * <p><b>What could not be composed is an answer and never an absence.</b> A row short of a stand-in
 * its target requires is a row nothing applies, and one that wants a table no module states is one
 * this compiler does not write — both are said in the words a search comes back with, so that no
 * reader downstream has to work out what an empty list meant.
 *
 * @param requires what the behavior has to stand in for, in the order it requires them
 * @param standing one subject per dependency a value can be composed for, and no entry for one
 *                 whose answer no position stands at. Handed in rather than made: where a reading
 *                 of a type is made is where every reading of a behavior's input is made
 * @param blocks   what the module's {@code fake} blocks declare, which is what says whether a
 *                 dependency is answered without the row writing anything
 */
record AnswersForARule(RequiredDependencies requires,
                       Map<ValueName.Behavior, AnswerSubjects> standing,
                       FakeTables blocks) {

    /**
     * Every way a row taking {@code demanded} could stand the dependencies in, or the one answer
     * saying nothing stands them in.
     *
     * <p>Several where a way leaves the case of a union answer open: each case a value composes for
     * is a row the way admits, and which of them reaches what is not something a reading of the way
     * says. They are searched with rather than chosen between, so what a search comes to about a
     * model does not follow from which of them was taken first.
     *
     * <p>The ways of the dependencies taken together, which is why this is a product. Two
     * dependencies each left open are answered by a row apiece, and a walk pairing them off would
     * search some of the rows a way admits and report about the model as though it had searched
     * them all.
     */
    List<StandInAttempt> of(AnswersDemanded demanded) {
        List<DemandGap> unaccounted = new ArrayList<>(demanded.declined());
        Map<ValueName.Behavior, Map<InjectedAnswer, List<AnswerDemand>>> asked = byDependency(
                demanded.byAnswer());
        List<List<StoodInAnswer>> apiece = new ArrayList<>();
        for (RequiredDependencies.Required each : requires.inOrder()) {
            StandingIn here = standingIn(each, asked.getOrDefault(each.dependency(), Map.of()));
            unaccounted.addAll(here.unaccounted());
            if (here instanceof StandingIn.None(var why, var _)) {
                return List.of(new StandInAttempt(new AnswersStoodIn.NothingComposed(why),
                        account(demanded, unaccounted)));
            }
            apiece.add(((StandingIn.Any) here).alternatives());
        }
        CompositionAccount account = account(demanded, unaccounted);
        List<StandInAttempt> out = new ArrayList<>();
        for (List<StoodInAnswer> combination : everyCombinationOf(apiece)) {
            out.add(new StandInAttempt(new AnswersStoodIn.Stood(combination), account));
        }
        return List.copyOf(out);
    }

    /**
     * What the answer side of the way came to, as one value beside whatever was stood in.
     *
     * <p>Both of what it holds come from here rather than from the caller: which conditions this
     * side answered for is the reading's ({@link AnswersDemanded#takenUp()}) and what it fell short
     * of is what the stages below wrote down. Worked out where the two are in hand, so that the
     * reconciliation of the two projections is not a reading anybody downstream repeats.
     */
    private static CompositionAccount account(AnswersDemanded demanded,
                                              List<DemandGap> unaccounted) {
        // One entry per demand nothing was composed against, however many times it was asked. A
        // union answer is composed for case by case and a demand none of them carries comes back
        // once per case, which is this reading's arithmetic rather than anything about the
        // condition.
        return new CompositionAccount(List.of(),
                unaccounted.isEmpty() ? List.of()
                        : List.copyOf(new LinkedHashSet<>(unaccounted)),
                demanded.takenUp());
    }

    /**
     * One list per way of answering every dependency, in the order the alternatives are enumerated
     * in.
     *
     * <p>A behavior requiring nothing has one way of answering nothing, which is what the product of
     * no lists is. Written as an empty list of ways, a row of such a behavior would be a row nothing
     * composes.
     */
    private static List<List<StoodInAnswer>> everyCombinationOf(List<List<StoodInAnswer>> apiece) {
        List<List<StoodInAnswer>> out = new ArrayList<>();
        out.add(List.of());
        for (List<StoodInAnswer> alternatives : apiece) {
            List<List<StoodInAnswer>> wider = new ArrayList<>();
            for (List<StoodInAnswer> already : out) {
                for (StoodInAnswer each : alternatives) {
                    List<StoodInAnswer> both = new ArrayList<>(already);
                    both.add(each);
                    wider.add(List.copyOf(both));
                }
            }
            out = wider;
        }
        return out;
    }

    /**
     * What one dependency can be stood in with, or why nothing stands it in.
     *
     * <p>Alternatives and not one answer, for the reason {@link #of} is a product: a dependency
     * whose case a way leaves open has a value apiece and every one of them is a row.
     */
    private sealed interface StandingIn {

        /** What of the way this dependency's value was not composed against, which either answer
         *  may have. */
        List<DemandGap> unaccounted();

        /** The ways it can be answered, every one of which composes a row. */
        record Any(List<StoodInAnswer> alternatives, List<DemandGap> unaccounted)
                implements StandingIn {

            public Any {
                alternatives = List.copyOf(alternatives);
                unaccounted = List.copyOf(unaccounted);
                if (alternatives.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a dependency something stands in for has a way of standing in");
                }
            }
        }

        /** Nothing does, in the words a search comes back with. */
        record None(Generator.UnresolvedCombination.Reason why, List<DemandGap> unaccounted)
                implements StandingIn {

            public None {
                unaccounted = List.copyOf(unaccounted);
            }
        }
    }

    /**
     * What one dependency is stood in with.
     *
     * <p>A dependency the way asks nothing of is left to the module where the module answers it,
     * and answered with a value of the row's own where nothing else does: what such a row needs is
     * something to run against, and where the module already says what that is, saying it again on
     * the row puts this row somewhere none of the module's own rows are.
     *
     * <p>A dependency the way does ask something of is answered by the row wherever one value
     * serves every asking, that being the one thing that certainly meets what the way asks. Where
     * no such value composes, the module's table stands where it states one — the way may be one
     * the module was written for — and what the run reaches decides whether it was.
     */
    private StandingIn standingIn(RequiredDependencies.Required required,
                                  Map<InjectedAnswer, List<AnswerDemand>> asked) {
        if (asked.isEmpty() && stated(required.dependency())) {
            return byTheModule(required, List.of());
        }
        List<DemandGap> unaccounted = new ArrayList<>();
        Map<InjectedAnswer, List<Candidate>> values = new LinkedHashMap<>();
        for (Map.Entry<InjectedAnswer, List<AnswerDemand>> each : asked.entrySet()) {
            Composing composed = composed(required, each.getValue());
            unaccounted.addAll(composed.unaccounted());
            if (composed.values().isEmpty()) {
                // The row leans on the table the module states, which is a row that runs and not
                // a row composed against what the way asks. What it was not composed against
                // travels with it: a run of such a row that lands somewhere else says something
                // about a value nothing here could build, and nothing about the model.
                return stated(required.dependency()) ? byTheModule(required, unaccounted)
                        : nothingStandsIn(unaccounted);
            }
            values.put(each.getKey(), composed.values());
        }
        List<Candidate> serving = servingEveryAsking(required, values);
        if (!serving.isEmpty()) {
            List<StoodInAnswer> alternatives = new ArrayList<>();
            for (Candidate each : serving) {
                alternatives.add(new StoodInAnswer.OnTheRow(required.dependency(), each.value()));
            }
            return new StandingIn.Any(alternatives, unaccounted);
        }
        // The way wants the dependency to answer differently at different calls, which wants a
        // table — written once for a module and part of the environment several rows share rather
        // than part of a row. Nothing here composes one, so the row leans on the one the module
        // states, and where the module states none there is nothing for this way to be tried with.
        return stated(required.dependency()) ? byTheModule(required, unaccounted)
                : new StandingIn.None(
                        Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS,
                        unaccounted);
    }

    /**
     * Whether the module answers {@code dependency} for whatever a row asks of it.
     *
     * <p>Both halves, and the second is not a reading of what this way needs. A table the module
     * states with no {@code _} row answers the calls its rows state and refuses the rest, and a row
     * leaning on it is a row that fails where it is pasted the moment it asks about anything else —
     * which is a call only running the row finds, and which the surfaces that offer a row without
     * running it would never find at all.
     *
     * <p>So what is asked here is of the table alone: can it refuse a call. A way whose calls a
     * partial table happens to answer is a row this compiler then does not offer, which is a row
     * lost rather than a row wrong — and the answer for such a way is the one it had before, that a
     * table is what it needs and this compiler writes none.
     */
    private boolean stated(ValueName.Behavior dependency) {
        return ExampleProvisioning.standingIn(List.of(), dependency, blocks)
                instanceof ExampleProvisioning.Standin.InTheModule(var table)
                && ExampleStatements.answersEveryCall(table.read());
    }

    private static StandingIn byTheModule(RequiredDependencies.Required required,
                                          List<DemandGap> unaccounted) {
        return new StandingIn.Any(
                List.of(new StoodInAnswer.InTheModule(required.dependency())), unaccounted);
    }

    private static StandingIn nothingStandsIn(List<DemandGap> unaccounted) {
        return new StandingIn.None(
                Generator.UnresolvedCombination.Reason.NOTHING_STANDS_IN_FOR_A_DEPENDENCY,
                unaccounted);
    }

    /**
     * Every value that serves every asking, which is what the askings have in common.
     *
     * <p>Asked of what the row would write, which is what a {@code with} is. It is not a question
     * about which askings are one — that is {@link InjectedAnswer}'s and was settled where the body
     * was read — but about whether one value answers the askings a row makes.
     *
     * <p>An intersection and not a comparison of two, because an asking may leave several values
     * open: two askings that leave the cases of a union open leave the cases they share, and a walk
     * taking one apiece and comparing them would find two askings with a value in common to have
     * none.
     *
     * <p>What tells two candidates apart is {@link Candidate#writes}, which is what a row writes
     * for the value. Each asking composes its own value, so two answers to one asking are alike in
     * what a row would write and need not be alike in how they were made.
     */
    private List<Candidate> servingEveryAsking(RequiredDependencies.Required required,
                                               Map<InjectedAnswer, List<Candidate>> values) {
        if (values.isEmpty()) {
            return composed(required, List.of()).values();
        }
        Map<WhatARowWrites, Candidate> serving = null;
        for (List<Candidate> each : values.values()) {
            Map<WhatARowWrites, Candidate> here = new LinkedHashMap<>();
            each.forEach(candidate -> here.putIfAbsent(candidate.writes(), candidate));
            if (serving == null) {
                serving = here;
            } else {
                serving.keySet().retainAll(here.keySet());
            }
        }
        return List.copyOf(serving.values());
    }

    /**
     * Every value of the dependency's answer meeting {@code demands}, and what no value was
     * composed against.
     *
     * <p>Both, and the second is not read off the first being short. A value composed for one case
     * of a union and nothing composed for another leave one candidate and a demand that reached
     * nothing; an account taken from the empty list would be written only where every case came to
     * nothing.
     */
    private Composing composed(RequiredDependencies.Required required,
                               List<AnswerDemand> demands) {
        AnswerSubjects subjects = standing.get(required.dependency());
        if (subjects == null) {
            // No position stands at what the dependency answers, so there is nothing here to
            // compose over and no demand that anything fell short of. What a reader is told is the
            // word beside it.
            return new Composing(List.of(), List.of());
        }
        List<Candidate> out = new ArrayList<>();
        List<DemandGap> unaccounted = new ArrayList<>();
        for (AnswerSubjects.Feasible each : subjects.against(demands)) {
            AnAnswerComposed.Attempt attempt =
                    AnAnswerComposed.of(each.standing(), each.demands());
            unaccounted.addAll(attempt.unaccounted());
            if (attempt.outcome() instanceof AnAnswerComposed.Outcome.Composed(var value)) {
                out.add(new Candidate(each.caseOfTheAnswer(), value));
            }
        }
        return new Composing(out, unaccounted);
    }

    /** The values composed for one asking, and what none of them was composed against. */
    private record Composing(List<Candidate> values, List<DemandGap> unaccounted) {

        private Composing {
            values = List.copyOf(values);
            unaccounted = List.copyOf(unaccounted);
        }
    }

    /**
     * One value a row could stand a dependency in with.
     *
     * <p>Two of these are one value where {@link #writes} says so, which is asked of the candidate
     * rather than left to what the two happen to be made of.
     *
     * @param caseOfTheAnswer which case of a union this is a value of, or null where the answer is
     *                        not a union
     */
    private record Candidate(TypeSymbol caseOfTheAnswer, FixtureTemplate value) {

        /**
         * What tells this candidate from another where the question is whether one value answers
         * every asking a row makes.
         *
         * <p>What a row writes, which is the answer {@link RowKey} gives to the same question about
         * a whole row. A {@code with} is a line of source and two askings are served by one value
         * when the row writes one line for both of them, so that is what is compared — the case
         * beside it, which is the fact a candidate carries that the line is of.
         *
         * <p><b>And not the value as it is made.</b> A {@link FixtureTemplate} holds the tree a
         * decoder builds as well as the text, and a name inside that tree carries which reference
         * of a declaration the run composed — a number minted to tell two occurrences apart
         * ({@link souther.compiler.types.FixtureReferenceOrigin}). Compared as it is made, two
         * askings answered by one value would be two the moment the value is a name, because each
         * asking composed its own occurrence of it.
         */
        WhatARowWrites writes() {
            return new WhatARowWrites(caseOfTheAnswer, value.text());
        }
    }

    /** One value as a row writes it, which is what two askings have in common or do not. */
    private record WhatARowWrites(TypeSymbol caseOfTheAnswer, String written) {}

    /** The askings of each dependency, in the order they were first asked about. */
    private static Map<ValueName.Behavior, Map<InjectedAnswer, List<AnswerDemand>>> byDependency(
            Map<InjectedAnswer, List<AnswerDemand>> byAnswer) {
        Map<ValueName.Behavior, Map<InjectedAnswer, List<AnswerDemand>>> out =
                new LinkedHashMap<>();
        byAnswer.forEach((answer, demands) -> out
                .computeIfAbsent(answer.dependency(), _ -> new LinkedHashMap<>())
                .put(answer, demands));
        return out;
    }
}
