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
        Map<ValueName.Behavior, Map<InjectedAnswer, List<AnswerDemand>>> asked = byDependency(
                demanded.byAnswer());
        List<List<Alternative>> apiece = new ArrayList<>();
        // What is known where no row of this comes of any of it, which is the evidence of the
        // dependencies decided so far. A demand one of them composed a value for is one something
        // composed a value for however the standing-in then ended, and reading it as a demand
        // nothing met would put this compiler's word on a value it has.
        Evidence withoutARow = Evidence.NOTHING;
        for (RequiredDependencies.Required each : requires.inOrder()) {
            StandingIn here = standingIn(each, asked.getOrDefault(each.dependency(), Map.of()));
            if (here instanceof StandingIn.None(var why, var evidence)) {
                return List.of(new StandInAttempt(new AnswersStoodIn.NothingComposed(why),
                        account(demanded, withoutARow.and(evidence))));
            }
            withoutARow = withoutARow.and(((StandingIn.Any) here).whereNoRowIsChosen());
            apiece.add(((StandingIn.Any) here).alternatives());
        }
        List<StandInAttempt> out = new ArrayList<>();
        for (List<Alternative> combination : everyCombinationOf(apiece)) {
            // What this row met, and not what was tried for it. A union answer is composed case by
            // case and a case that came to nothing is not what the row carries — read as the row's
            // shortfall, a row composed against everything the way asks would be reported as short
            // of it.
            List<StoodInAnswer> stood = new ArrayList<>();
            Evidence evidence = Evidence.NOTHING;
            for (Alternative each : combination) {
                stood.add(each.stood());
                evidence = evidence.and(each.evidence());
            }
            out.add(new StandInAttempt(new AnswersStoodIn.Stood(stood),
                    account(demanded, evidence)));
        }
        return List.copyOf(out);
    }

    /**
     * One way of standing one dependency in, and the evidence about the demands that value left.
     *
     * <p>The evidence and not one half of it. Which demands a value met and what a stage said of
     * the ones it did not are answers about the same value, and the account reads them together —
     * so they travel as one thing rather than as two lists a caller pairs off. Handed over
     * separately, the two came from different places: what every case of a union could not do was
     * read beside what the one case the row carries met.
     */
    private record Alternative(StoodInAnswer stood, Evidence evidence) {}

    /**
     * What is known about the demands of one asking, from one value or from the absence of one.
     *
     * <p>Both halves at one scope, which is the whole of why this is a value. What a row is short
     * of is taken as what the way stated less what this met, with what a stage said kept for its
     * wording — and the two halves read together are an answer about one row only where they are
     * about one row.
     *
     * @param met  the demands a value was composed against
     * @param said what a stage had to say about demands no value here met, which may be nothing
     */
    private record Evidence(List<AnswerDemand> met, List<DemandGap> said) {

        static final Evidence NOTHING = new Evidence(List.of(), List.of());

        private Evidence {
            met = List.copyOf(met);
            said = List.copyOf(said);
        }

        /** One that met nothing, and says what a stage said of the asking it was. */
        static Evidence metNothing(List<DemandGap> said) {
            return new Evidence(List.of(), said);
        }

        /** The two together, which is what a row standing several dependencies in leaves. */
        Evidence and(Evidence more) {
            List<AnswerDemand> bothMet = new ArrayList<>(met);
            bothMet.addAll(more.met);
            List<DemandGap> bothSaid = new ArrayList<>(said);
            bothSaid.addAll(more.said);
            return new Evidence(bothMet, bothSaid);
        }
    }

    /**
     * What the answer side of the way came to, as one value beside whatever was stood in.
     *
     * <p><b>Every demand the way stated, and not the ones a walk reached.</b> The account is what
     * the row was not composed against, so it is the difference between what the way asks and what
     * the row met — taken here, where the whole of what the way asks is in hand. Accumulated as a
     * walk goes instead, a demand is lost wherever an asking ends early: the dependency whose
     * stand-in came to nothing is not asked about again, the ones after it are not asked at all,
     * and the conditions of every one of them are ones the reading took up, so the account of the
     * way over the input drops them too and nothing anywhere names them.
     *
     * <p>What a composer said of a demand is kept where it said something, since it says which
     * stage let the demand go and why; a demand nothing said anything about is what this adds.
     */
    private static CompositionAccount account(AnswersDemanded demanded, Evidence of) {
        List<DemandGap> gaps = new ArrayList<>(demanded.declined());
        // What was said of a demand this one did meet is another value's answer and not this
        // one's, which is what keeps the two halves of the evidence one value: a case that came to
        // nothing is not what the row carries, and neither is what that case could not do.
        of.said().stream().filter(gap -> !(gap instanceof DemandGap.Uncomposed(var about, var _)
                && of.met().contains(about))).forEach(gaps::add);
        for (AnswerDemand each : demanded.stated()) {
            if (!of.met().contains(each) && !named(of.said(), each)) {
                gaps.add(new DemandGap.Uncomposed(each,
                        new DemandGap.WhyNotComposed.NothingComposedAValueOfTheAnswer()));
            }
        }
        // One entry per demand nothing was composed against, however many times it was asked. A
        // union answer is composed for case by case and a demand none of them carries comes back
        // once per case, which is this reading's arithmetic rather than anything about the
        // condition.
        return new CompositionAccount(List.of(),
                gaps.isEmpty() ? List.of() : List.copyOf(new LinkedHashSet<>(gaps)),
                demanded.takenUp());
    }

    /** Whether one of these already says what became of {@code demand}. */
    private static boolean named(List<DemandGap> said, AnswerDemand demand) {
        return said.stream().anyMatch(gap -> gap instanceof DemandGap.Uncomposed(
                AnswerDemand of, var _) && of.equals(demand));
    }

    /**
     * One list per way of answering every dependency, in the order the alternatives are enumerated
     * in.
     *
     * <p>A behavior requiring nothing has one way of answering nothing, which is what the product of
     * no lists is. Written as an empty list of ways, a row of such a behavior would be a row nothing
     * composes.
     */
    private static List<List<Alternative>> everyCombinationOf(List<List<Alternative>> apiece) {
        List<List<Alternative>> out = new ArrayList<>();
        out.add(List.of());
        for (List<Alternative> alternatives : apiece) {
            List<List<Alternative>> wider = new ArrayList<>();
            for (List<Alternative> already : out) {
                for (Alternative each : alternatives) {
                    List<Alternative> both = new ArrayList<>(already);
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

        /**
         * The ways it can be answered, each with the evidence its own value leaves, and the
         * evidence for a caller that ends with no row at all.
         *
         * <p>Two scopes because there are two questions, and each is answered at its own. What a
         * row carries is one of these alternatives and nothing about the others; what is known
         * where no row is composed is that some value of this dependency met what it met, whichever
         * alternative it was.
         */
        record Any(List<Alternative> alternatives, Evidence whereNoRowIsChosen)
                implements StandingIn {

            public Any {
                alternatives = List.copyOf(alternatives);
                if (alternatives.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a dependency something stands in for has a way of standing in");
                }
            }
        }

        /** Nothing does, in the words a search comes back with. */
        record None(Generator.UnresolvedCombination.Reason why, Evidence evidence)
                implements StandingIn {}
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
            return byTheModule(required, Evidence.NOTHING);
        }
        Map<InjectedAnswer, List<Candidate>> values = new LinkedHashMap<>();
        List<DemandGap> said = new ArrayList<>();
        List<AnswerDemand> metBySomething = new ArrayList<>();
        for (Map.Entry<InjectedAnswer, List<AnswerDemand>> each : asked.entrySet()) {
            Composing composed = composed(required, each.getValue());
            said.addAll(composed.written());
            composed.values().forEach(candidate -> metBySomething.addAll(candidate.met()));
            if (composed.values().isEmpty()) {
                // The row leans on the table the module states, which is a row that runs and not
                // a row composed against what the way asks. Nothing of this dependency is met by
                // it — not the asking that came to nothing, not the askings a value was composed
                // for and the row does not write, and not the ones after this one, which are not
                // asked at all. Which demands those are is the account's to say, and it says it of
                // what the way stated rather than of what this loop reached.
                Evidence evidence = new Evidence(metBySomething, said);
                return stated(required.dependency()) ? byTheModule(required, evidence)
                        : nothingStandsIn(evidence);
            }
            values.put(each.getKey(), composed.values());
        }
        List<Candidate> serving = servingEveryAsking(required, values);
        if (!serving.isEmpty()) {
            List<Alternative> alternatives = new ArrayList<>();
            for (Candidate each : serving) {
                alternatives.add(new Alternative(
                        new StoodInAnswer.OnTheRow(required.dependency(), each.value()),
                        new Evidence(each.met(), each.said())));
            }
            // And where no row comes of the standing-in at all, what some value of this dependency
            // met is still met: the demands under it were composed for, whatever then ended the
            // rest. Read as the row's own, it would answer for a value the row does not carry.
            return new StandingIn.Any(alternatives, new Evidence(metBySomething, said));
        }
        // The way wants the dependency to answer differently at different calls, which wants a
        // table — written once for a module and part of the environment several rows share rather
        // than part of a row. Nothing here composes one, so the row leans on the one the module
        // states, and where the module states none there is nothing for this way to be tried with.
        //
        // Said of every demand of every asking, because that is what such a row does not meet: the
        // values that were composed answer one asking apiece and the row writes none of them.
        List<DemandGap> everyAsking = new ArrayList<>(said);
        asked.values().forEach(demands -> demands.forEach(demand ->
                everyAsking.add(new DemandGap.Uncomposed(demand,
                        new DemandGap.WhyNotComposed.OneValueAnswersEveryCall()))));
        Evidence wanting = new Evidence(metBySomething, everyAsking);
        return stated(required.dependency()) ? byTheModule(required, wanting)
                : new StandingIn.None(
                        Generator.UnresolvedCombination.Reason.A_TABLE_IS_WHAT_THIS_NEEDS, wanting);
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

    /**
     * A row that leans on the table the module states.
     *
     * <p>The row meets nothing the way asks of the dependency, since what it writes for it is
     * nothing: a value this composed for one asking is a value that row does not carry. What is
     * known where no row comes of the standing-in at all is the other question and keeps what was
     * composed, which is why the two are handed over apart.
     */
    private static StandingIn byTheModule(RequiredDependencies.Required required,
                                          Evidence evidence) {
        return new StandingIn.Any(List.of(new Alternative(
                new StoodInAnswer.InTheModule(required.dependency()),
                Evidence.metNothing(evidence.said()))), evidence);
    }

    private static StandingIn nothingStandsIn(Evidence evidence) {
        return new StandingIn.None(
                Generator.UnresolvedCombination.Reason.NOTHING_STANDS_IN_FOR_A_DEPENDENCY,
                evidence);
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
                // What the one value was not composed against, over every asking it serves. The
                // row writes one line for all of them, so a demand of any asking that nothing was
                // composed against is a demand that line does not meet.
                serving.replaceAll((writes, candidate) -> candidate.and(here.get(writes)));
            }
        }
        return List.copyOf(serving.values());
    }

    /**
     * Every value of the dependency's answer meeting {@code demands}, each with what it was not
     * composed against, and what the composers wrote down beside them.
     *
     * <p>The first is the row's and the second is for a caller that has no row. A value composed
     * for one case of a union carries what that value was short of; a case that came to nothing is
     * not what the row carries and its answers are read only where no case gave one.
     */
    private Composing composed(RequiredDependencies.Required required,
                               List<AnswerDemand> demands) {
        AnswerSubjects subjects = standing.get(required.dependency());
        List<AnswerSubjects.Feasible> over = subjects == null ? List.of()
                : subjects.against(demands);
        List<Candidate> out = new ArrayList<>();
        List<DemandGap> written = new ArrayList<>();
        for (AnswerSubjects.Feasible each : over) {
            AnAnswerComposed.Attempt attempt =
                    AnAnswerComposed.of(each.standing(), each.demands());
            written.addAll(attempt.unaccounted());
            if (attempt.outcome() instanceof AnAnswerComposed.Outcome.Composed(var value)) {
                // This value's own evidence, and never the asking's: what another case could not
                // put under a value of its own is nothing about the value this is.
                out.add(new Candidate(each.caseOfTheAnswer(), value,
                        met(demands, attempt.unaccounted()), attempt.unaccounted()));
            }
        }
        return new Composing(out, written);
    }

    /**
     * What a composed value meets of the asking, which is what was asked less what the composing
     * says it could not put under the value.
     *
     * <p>Asked of the asking and not of what was handed to the composer. Choosing the case of a
     * union answers the demand that named it and that demand does not travel on
     * ({@link AnswerSubjects#against}), so a value read as meeting only what it was handed would
     * be read as short of the case it is a value of.
     */
    private static List<AnswerDemand> met(List<AnswerDemand> demands, List<DemandGap> unaccounted) {
        List<AnswerDemand> out = new ArrayList<>();
        for (AnswerDemand each : demands) {
            if (!named(unaccounted, each)) {
                out.add(each);
            }
        }
        return out;
    }

    /**
     * The values composed for one asking, and what nothing was composed against where none was.
     *
     * <p>Two things and not one list, because they answer to two readers. What a value was composed
     * without travels with that value ({@link Candidate}), since it is that row's; what is here is
     * for the case there is no row of this compiler's to carry it, where the account belongs to
     * whatever the row leans on instead.
     */
    private record Composing(List<Candidate> values, List<DemandGap> written) {

        private Composing {
            values = List.copyOf(values);
            written = List.copyOf(written);
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
    private record Candidate(TypeSymbol caseOfTheAnswer, FixtureTemplate value,
                             List<AnswerDemand> met, List<DemandGap> said) {

        private Candidate {
            met = List.copyOf(met);
            said = List.copyOf(said);
        }

        /** This value, with what it met and did not meet of another asking it serves too. */
        Candidate and(Candidate serving) {
            if (serving == null) {
                return this;
            }
            List<AnswerDemand> bothMet = new ArrayList<>(met);
            bothMet.addAll(serving.met);
            List<DemandGap> bothSaid = new ArrayList<>(said);
            bothSaid.addAll(serving.said);
            return new Candidate(caseOfTheAnswer, value, bothMet, bothSaid);
        }

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
