package souther.compiler.query;

import souther.compiler.check.FakeTables;
import souther.compiler.examples.ExampleProvisioning;
import souther.compiler.examples.ExampleStatements;
import souther.compiler.partition.AnAnswerComposed;
import souther.compiler.partition.AnswerDemand;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.AnswersStoodIn;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.Generator;
import souther.compiler.partition.InjectedAnswer;
import souther.compiler.partition.StoodInAnswer;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
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
    List<AnswersStoodIn> of(AnswersDemanded demanded) {
        if (!demanded.whole()) {
            // The way asks something of an answer that nothing here states, so a value composed
            // against the rest would be composed against part of what the row has to be.
            return List.of(new AnswersStoodIn.NothingComposed(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE));
        }
        Map<ValueName.Behavior, Map<InjectedAnswer, List<AnswerDemand>>> asked = byDependency(
                demanded.byAnswer());
        List<List<StoodInAnswer>> apiece = new ArrayList<>();
        for (RequiredDependencies.Required each : requires.inOrder()) {
            StandingIn here = standingIn(each, asked.getOrDefault(each.dependency(), Map.of()));
            if (here instanceof StandingIn.None(var why)) {
                return List.of(new AnswersStoodIn.NothingComposed(why));
            }
            apiece.add(((StandingIn.Any) here).alternatives());
        }
        List<AnswersStoodIn> out = new ArrayList<>();
        for (List<StoodInAnswer> combination : everyCombinationOf(apiece)) {
            out.add(new AnswersStoodIn.Stood(combination));
        }
        return List.copyOf(out);
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

        /** The ways it can be answered, every one of which composes a row. */
        record Any(List<StoodInAnswer> alternatives) implements StandingIn {

            public Any {
                alternatives = List.copyOf(alternatives);
                if (alternatives.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a dependency something stands in for has a way of standing in");
                }
            }
        }

        /** Nothing does, in the words a search comes back with. */
        record None(Generator.UnresolvedCombination.Reason why) implements StandingIn {}
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
            return byTheModule(required);
        }
        Map<InjectedAnswer, List<Candidate>> values = new LinkedHashMap<>();
        for (Map.Entry<InjectedAnswer, List<AnswerDemand>> each : asked.entrySet()) {
            List<Candidate> composed = composed(required, each.getValue());
            if (composed.isEmpty()) {
                return stated(required.dependency()) ? byTheModule(required) : nothingStandsIn();
            }
            values.put(each.getKey(), composed);
        }
        List<Candidate> serving = servingEveryAsking(required, values);
        if (!serving.isEmpty()) {
            List<StoodInAnswer> alternatives = new ArrayList<>();
            for (Candidate each : serving) {
                alternatives.add(new StoodInAnswer.OnTheRow(required.dependency(), each.value()));
            }
            return new StandingIn.Any(alternatives);
        }
        // The way wants the dependency to answer differently at different calls, which wants a
        // table — written once for a module and part of the environment several rows share rather
        // than part of a row. Nothing here composes one, so the row leans on the one the module
        // states, and where the module states none there is nothing for this way to be tried with.
        return stated(required.dependency()) ? byTheModule(required)
                : new StandingIn.None(
                        Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS);
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

    private static StandingIn byTheModule(RequiredDependencies.Required required) {
        return new StandingIn.Any(
                List.of(new StoodInAnswer.InTheModule(required.dependency())));
    }

    private static StandingIn nothingStandsIn() {
        return new StandingIn.None(
                Generator.UnresolvedCombination.Reason.NOTHING_STANDS_IN_FOR_A_DEPENDENCY);
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
     * <p>What tells two candidates apart is the value, which is the case it is of and everything
     * written under it — held as the value rather than as the line it prints as, a reading of one
     * asking and a reading of the other agreeing would be two spellings agreeing.
     */
    private List<Candidate> servingEveryAsking(RequiredDependencies.Required required,
                                               Map<InjectedAnswer, List<Candidate>> values) {
        if (values.isEmpty()) {
            return composed(required, List.of());
        }
        List<Candidate> serving = null;
        for (List<Candidate> each : values.values()) {
            if (serving == null) {
                serving = new ArrayList<>(each);
            } else {
                serving.retainAll(each);
            }
        }
        return List.copyOf(serving);
    }

    /** Every value of the dependency's answer meeting {@code demands}, and none where none was
     *  composed. */
    private List<Candidate> composed(RequiredDependencies.Required required,
                                     List<AnswerDemand> demands) {
        AnswerSubjects subjects = standing.get(required.dependency());
        if (subjects == null) {
            return List.of();
        }
        List<Candidate> out = new ArrayList<>();
        for (AnswerSubjects.Feasible each : subjects.against(demands)) {
            if (AnAnswerComposed.of(each.standing(), each.demands())
                    instanceof AnAnswerComposed.Outcome.Composed(var value)) {
                out.add(new Candidate(each.caseOfTheAnswer(), value));
            }
        }
        return List.copyOf(out);
    }

    /**
     * One value a row could stand a dependency in with.
     *
     * <p>The case beside the value, so that what two askings have in common is asked of what the
     * candidate is rather than of the words it is written with. Two candidates of one case carrying
     * different values are two candidates, which is what a demand about a place inside an answer
     * leaves.
     *
     * @param caseOfTheAnswer which case of a union this is a value of, or null where the answer is
     *                        not a union
     */
    private record Candidate(TypeSymbol caseOfTheAnswer, FixtureTemplate value) {}

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
