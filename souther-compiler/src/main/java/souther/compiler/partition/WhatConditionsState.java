package souther.compiler.partition;

import souther.compiler.check.ComparisonClaim;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.inputs.ReadMeaning;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.OptionalInt;
import java.util.Set;
import java.util.function.Supplier;

/**
 * What each condition met over one reading of the input states, read once however many readers
 * ask.
 *
 * <p>A comparison a fork tests is asked what it states three times over: for what a row coming out
 * each way of the fork has done, and for the line it draws. Those are one statement, read under
 * the same names, so it is read once and each reader takes it from here. A truth a fork tests is
 * asked once for each way, and is the same.
 *
 * <p>Keyed on the nodes and not on what they are equal to. A comparison is the node it is written
 * as, and two nodes alike in every part are two comparisons in two places that may be read under
 * different names; the names are the other half of the key. A comparison this compiler composes
 * where it is asked, such as an emptiness check read as a size against nought, is a new node each
 * time and is read each time.
 *
 * <p>Of one reading of the input, which is held and asked for: a statement is read against the
 * input's declarations as well as its names, and an answer under one reading is no answer under
 * another. And one for that reading, kept with it ({@link InputReading#derived}): the readers of
 * one input — the lines drawn, the ways to them, the decisions, the guards — ask about the same
 * conditions, and one kept by each of them would read every condition once per reader.
 *
 * <p>The arms of a fork that chooses by no condition are kept here too, every arm of a fork at
 * once ({@link Pullback#ofTheArms}): what one arm states is a fact of the whole fork, so it is
 * read once for the fork and not once for each arm a reader asks about.
 *
 * <p>And what keeps each occurrence of a container written out ({@link #kept}), which is one of
 * these: a filter's truth on the element, or the arm of a fork the occurrence was written in. A
 * walk writes out every occurrence of an arm under the same fork, and every reader of an occurrence
 * asks what keeps it, so read anywhere else the fork would be read once for each occurrence and
 * each reader.
 *
 * <p>Read without a site of the model, this is the only place they are read: what a reader asks
 * for here is what every other reader of the same reading was answered. A reading filed at a site
 * ({@code MeaningsOfABodyReading}) says which construct it is the meaning of, and is that one's.
 */
final class WhatConditionsState {

    private final InputReading read;
    private final Map<AComparison, Pullback.OnTheInput> comparisons = new HashMap<>();
    private final Map<ANode, Pullback.Pulled> truths = new HashMap<>();
    private final Map<ANode, Pullback.Pulled> presences = new HashMap<>();
    private final Map<ANode, List<Pullback.Pulled>> arms = new HashMap<>();
    private final Map<ANode, Optional<DividedInput>> dividedInputs = new HashMap<>();
    private final Map<ANode, Optional<Proposition>> operatorsAnswer = new HashMap<>();
    private final Map<Proposition, Proposition> denials = new IdentityHashMap<>();

    private WhatConditionsState(InputReading read) {
        this.read = read;
    }

    /** What the conditions met over {@code read} state, kept for that reading. */
    static WhatConditionsState of(InputReading read) {
        return read.derived(WhatConditionsState.class, WhatConditionsState::new);
    }

    /** A comparison, by the nodes its sides are and what its operator placed, under names. */
    private record AComparison(Core left, Core right, ComparisonClaim claim, InputReads reads) {

        @Override
        public boolean equals(Object other) {
            return other instanceof AComparison that && left == that.left && right == that.right
                    && claim.equals(that.claim) && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            int hash = System.identityHashCode(left);
            hash = hash * 31 + System.identityHashCode(right);
            hash = hash * 31 + claim.hashCode();
            return hash * 31 + reads.hashCode();
        }
    }

    /** A truth, or a fork whose arms are entered, by the node it is, under names. */
    record ANode(Core value, InputReads reads) {

        @Override
        public boolean equals(Object other) {
            return other instanceof ANode that && value == that.value && reads.equals(that.reads);
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(value) * 31 + reads.hashCode();
        }
    }

    /** What {@code comparison} states with its names as {@code reads} has them, under
     *  {@code read}. */
    Pullback.OnTheInput comparison(StatedComparison comparison, InputReads reads,
                                   InputReading read) {
        heldTo(read);
        return kept(comparisons,
                new AComparison(comparison.left(), comparison.right(), comparison.claim(), reads),
                () -> Pullback.ofAComparisonOnTheInput(comparison, reads, read));
    }

    /** Where every operator {@code body} works out answers with its names as {@code reads} has
     *  them, under {@code read} ({@link Pullback#whereItsOperatorsAnswer}) — empty where nothing
     *  says it answers only somewhere. */
    Optional<Proposition> whereItsOperatorsAnswer(Core body, InputReads reads,
                                                  InputReading read) {
        heldTo(read);
        return kept(operatorsAnswer, new ANode(body, reads), () -> Optional.ofNullable(
                Pullback.whereItsOperatorsAnswer(body, reads, read)));
    }

    /** What {@code truth} holding states with its names as {@code reads} has them, under
     *  {@code read}. */
    Pullback.Pulled truth(Core truth, InputReads reads, InputReading read) {
        heldTo(read);
        return kept(truths, new ANode(truth, reads),
                () -> Pullback.ofATruth(truth, reads, read, Optional.empty()));
    }

    /** What {@code optional} holding a value states with its names as {@code reads} has them,
     *  under {@code read}. */
    Pullback.Pulled presence(Core optional, InputReads reads, InputReading read) {
        heldTo(read);
        return kept(presences, new ANode(optional, reads),
                () -> Pullback.ofAPresence(optional, reads, read, Optional.empty()));
    }

    /** What a run entering arm {@code part} of {@code fork} states with its names as {@code reads}
     *  has them ({@link Pullback#ofTheArms}). */
    Pullback.Pulled arm(Core fork, int part, InputReads reads) {
        return kept(arms, new ANode(fork, reads),
                () -> Pullback.ofTheArms(fork, reads, read, Optional.empty())).get(part);
    }

    /**
     * The question a fork on a computed value asks of the input, and what each arm answers.
     *
     * @param of       the position the arms divide
     * @param question what the arms leave it, which is the answers of the one question
     * @param answered which of those the arm at an index leaves it. An arm the declarations already
     *                 decide asks nothing and has no entry
     */
    record DividedInput(DecisionSubject.AnInput of, Set<CasesLeft> question,
                        Map<Integer, CasesLeft> answered) {

        /** Kept for the whole reading, so held as the one meaning of the fork it is. The order is
         *  the arms', which a copy through {@code Set.copyOf} would not keep. */
        DividedInput {
            question = Collections.unmodifiableSet(new LinkedHashSet<>(question));
            answered = Collections.unmodifiableMap(new LinkedHashMap<>(answered));
        }
    }

    /**
     * The position of the input the arms of {@code fork} divide between them, where every arm
     * states a case of that one position and no two leave it a case in common; empty where an arm
     * states anything else, because nothing then says the arms divide it. What each leaves the
     * position is what the declarations leave it
     * ({@link ReachingCuts#taking(TermPath, CasesLeft, InputReading)}), as for a fork on the
     * position itself.
     *
     * <p>A fact of the whole fork, so read once for it and not once for each arm a reader asks
     * about.
     */
    Optional<DividedInput> inputDividedBy(Core.Match fork, InputReads reads) {
        return kept(dividedInputs, new ANode(fork, reads), () -> divide(fork, reads));
    }

    private Optional<DividedInput> divide(Core.Match fork, InputReads reads) {
        DecisionSubject.AnInput subject = null;
        Map<Integer, CasesLeft> answered = new LinkedHashMap<>();
        Set<Refinement> covered = new HashSet<>();
        for (int part = 0; part < fork.cases().size(); part++) {
            CaseOfAnInput stated = caseOfAnInput(arm(fork, part, reads).proposition());
            if (isNoCaseOf(subject, stated)) {
                return Optional.empty();
            }
            subject = stated.of();
            CasesLeft answer = switch (ReachingCuts.taking(subject.at(), stated.cases(), read)) {
                case DeclaredInput.Taking.Narrows(TermPath to) -> to.narrowing();
                case DeclaredInput.Taking.Excluded _ -> stated.cases();
                case DeclaredInput.Taking.Implied _ -> null;
            };
            if (answer != null) {
                for (Refinement atom : answer.atoms()) {
                    if (!covered.add(atom)) {
                        return Optional.empty();
                    }
                }
                answered.put(part, answer);
            }
        }
        return subject == null ? Optional.empty()
                : Optional.of(new DividedInput(subject,
                        new LinkedHashSet<>(answered.values()), answered));
    }

    /** Some cases of one input position, which is what an arm of a fork states of the input when
     *  it states nothing else. */
    private record CaseOfAnInput(DecisionSubject.AnInput of, CasesLeft cases) { }

    /**
     * The cases of one input position {@code stated} says the input is one of, or null where it
     * says anything else.
     *
     * <p>What a body that makes several cases one states is those cases held alternatively, and
     * what its last arm states is its own case held with every earlier arm's denied. Both are
     * cases of the one position, taken as the sets of distinctions they are: an alternative is
     * their union, a conjunction the cases it holds in common less the ones it denies. A denial
     * alone leaves a value every other case and is read as nothing, as is a statement about
     * another position or of another kind.
     */
    private static CaseOfAnInput caseOfAnInput(Proposition stated) {
        return switch (stated) {
            case Proposition.InCases(DecisionSubject.AnInput of, CasesLeft cases, boolean holds, _)
                    when holds -> new CaseOfAnInput(of, cases);
            case Proposition.Any(List<Proposition> parts, _) -> {
                DecisionSubject.AnInput of = null;
                Set<Refinement> atoms = new LinkedHashSet<>();
                for (Proposition part : parts) {
                    CaseOfAnInput one = caseOfAnInput(part);
                    if (isNoCaseOf(of, one)) {
                        yield null;
                    }
                    of = one.of();
                    atoms.addAll(one.cases().atoms());
                }
                yield casesOf(of, atoms);
            }
            case Proposition.All(List<Proposition> parts, _) -> {
                DecisionSubject.AnInput of = null;
                Set<Refinement> atoms = null;
                Set<Refinement> denied = new HashSet<>();
                for (Proposition part : parts) {
                    if (part instanceof Proposition.InCases(DecisionSubject.AnInput at,
                            CasesLeft cases, boolean holds, _) && !holds) {
                        if (of != null && !of.equals(at)) {
                            yield null;
                        }
                        of = at;
                        denied.addAll(cases.atoms());
                        continue;
                    }
                    CaseOfAnInput one = caseOfAnInput(part);
                    if (isNoCaseOf(of, one)) {
                        yield null;
                    }
                    of = one.of();
                    if (atoms == null) {
                        atoms = new LinkedHashSet<>(one.cases().atoms());
                    } else {
                        atoms.retainAll(one.cases().atoms());
                    }
                }
                if (atoms == null) {
                    yield null;
                }
                atoms.removeAll(denied);
                yield casesOf(of, atoms);
            }
            default -> null;
        };
    }

    /** Whether {@code one} is nothing said of the position {@code of} names, where it names one. */
    private static boolean isNoCaseOf(DecisionSubject.AnInput of, CaseOfAnInput one) {
        return one == null || (of != null && !of.equals(one.of()));
    }

    private static CaseOfAnInput casesOf(DecisionSubject.AnInput of, Set<Refinement> atoms) {
        CasesLeft cases = CasesLeft.ofEach(List.copyOf(atoms));
        return of == null || cases == null ? null : new CaseOfAnInput(of, cases);
    }

    /**
     * What an occurrence of a container written out being kept by {@code kept} states under
     * {@code read}: its truth coming out the way it was kept by, or its arm being the one a run
     * takes — each read as any truth or arm of a fork is here.
     */
    Proposition kept(ReadMeaning.Occurrence.Kept kept, InputReading read) {
        heldTo(read);
        return switch (kept) {
            case ReadMeaning.Occurrence.Kept.ATruth(Denotation truth, boolean holds,
                                                    OptionalInt _) -> {
                Proposition stated = truth(truth.value(), truth.at(), read).proposition();
                yield holds ? stated : denied(stated);
            }
            case ReadMeaning.Occurrence.Kept.AnArm(Denotation fork, int part) ->
                    arm(fork.value(), part, fork.at()).proposition();
        };
    }

    /**
     * What {@code in} keeps under {@code key}, read by {@code reading} the first time it is asked.
     *
     * <p>Asked and then put, and not computed in place: reading one condition reads others — a
     * truth an occurrence it walks over was kept by, an arm of a fork it stands in — and each of
     * those is kept here too, into the same map, while the first is still being read.
     */
    private static <K, V> V kept(Map<K, V> in, K key, Supplier<V> reading) {
        V known = in.get(key);
        if (known != null) {
            return known;
        }
        V made = reading.get();
        in.put(key, made);
        return made;
    }

    /**
     * What holds exactly where {@code stated} does not, made once for each statement kept here.
     *
     * <p>Kept by the statement it is the denial of, as the statement is kept by its node. A
     * condition coming out each way is asked for both, and a denial is made whole each time it is
     * asked: two of them are equal and two values, and a reader matching one against the other
     * compares them part by part, down every condition inside.
     */
    Proposition denied(Proposition stated) {
        return denials.computeIfAbsent(stated, Proposition::denied);
    }

    private void heldTo(InputReading asked) {
        if (asked != read) {
            throw new IllegalArgumentException(
                    "what a condition states is kept for one reading of the input, and was asked"
                            + " under another");
        }
    }
}
