package souther.compiler.meaning;

import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.BitSet;
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

/**
 * What in the model made the parts a case is taken apart on, read off how the statement was
 * derived.
 *
 * <p><b>From the parts the case is taken apart on, and from nothing else in the statement.</b> A
 * part is made at the step of the derivation whose conclusion first holds it: it is in what that
 * step concludes and in nothing any step under it concludes. What made it is what stands around
 * that step on the way down to it — the applications of closures it is read on, each the call
 * that applies the closure and which of its applications this is; the choice of the model whose
 * condition it is in; and a writing out of the ways elements are kept, where that is the step.
 * Parts are told apart as the cases are taken apart on them ({@link
 * WhereEachLineDecides#partsJoinedBy}), so a part made at two places was made at both, and one no
 * step is found to have made is counted as such and named after nothing.
 *
 * <p><b>Applications are told apart, and a body is not.</b> A closure's body is one construct on
 * every application, so a choice in it is one construct chosen once on each: how many times is
 * how many of its choosings the case is taken apart on parts of. One application inside another
 * of the same call — a walk carrying what the step before it answered — is that inner one.
 *
 * <p><b>And which helper wrote them, read off the same walk.</b> The constructs above are what
 * multiplied the parts, and a helper holding a {@code find} is named by them; the helper whose
 * comparisons a {@code find} applies on each candidate is not. So the walk also keeps the
 * innermost construct of the model each part was read at, and a helper is named
 * where the cases choose among its readings one beside another
 * ({@link CaseExpansion.MultipliedHelper}).
 *
 * <p><b>For a reader explaining a line, and nothing that reads the line.</b> Nothing here is a
 * figure the line stopped at, and past {@link #STEPS_A_READING_TAKES} what the parts came from is
 * not said, and the line is what it was.
 */
public final class TheChoicesACaseIsMadeOf {

    /**
     * How many steps of the derivations are walked, counting a step once for each way of reaching
     * it that stands under different constructs, before what made the parts is given up.
     */
    public static final int STEPS_A_READING_TAKES = 1 << 16;

    private TheChoicesACaseIsMadeOf() {
    }

    /**
     * What made the parts each of {@code cases} is taken apart on, read off {@code derivedBy}, in
     * the order the cases are given.
     *
     * <p>Every case of one statement at once: the derivations are concluded and walked once, for
     * the parts any of them is taken apart on, and each case is then told what made its own.
     */
    static List<CaseExpansion.Attribution> of(List<DecidingCase.Cases> cases,
                                              List<Derivation> derivedBy) {
        Walked walked = walk(cases, derivedBy);
        List<CaseExpansion.Attribution> out = new ArrayList<>();
        for (int at = 0; at < cases.size(); at++) {
            out.add(walked.why() != null ? walked.why()
                    : walked.reading().attributed(walked.each().get(at), cases.get(at)));
        }
        return out;
    }

    /**
     * The helpers whose readings the choices of each of {@code cases} stand among one beside
     * another, read off {@code derivedBy}, in the order the cases are given: none for a case
     * where the derivations show none, and for every case where they were not walked.
     *
     * <p>Nothing else of what made the parts is worked out, which is what a reader that tells
     * only the helper has no use for.
     */
    static List<List<CaseExpansion.MultipliedHelper>> helpersOf(List<DecidingCase.Cases> cases,
                                                                List<Derivation> derivedBy) {
        Walked walked = walk(cases, derivedBy);
        return cases.stream().map(each -> walked.why() != null
                ? List.<CaseExpansion.MultipliedHelper>of()
                : walked.reading().multiplied(each)).toList();
    }

    /** What the derivations came to when walked for the parts of the cases, or why they were
     *  not. */
    private record Walked(Reading reading, List<Set<Spelling>> each,
                          CaseExpansion.NotAttributed why) {}

    private static Walked walk(List<DecidingCase.Cases> cases, List<Derivation> derivedBy) {
        List<Set<Spelling>> each = cases.stream().map(TheChoicesACaseIsMadeOf::partsSplitOn)
                .toList();
        Set<Spelling> any = new HashSet<>();
        each.forEach(any::addAll);
        Reading reading = new Reading(any);
        if (derivedBy.isEmpty()) {
            return new Walked(reading, each,
                    new CaseExpansion.NotAttributed(CaseExpansion.WhyNotAttributed.NOTHING_DERIVED));
        }
        for (Derivation one : derivedBy) {
            if (!reading.from(one)) {
                return new Walked(reading, each, new CaseExpansion.NotAttributed(
                        CaseExpansion.WhyNotAttributed.STEPS_A_READING_TAKES));
            }
        }
        return new Walked(reading, each, null);
    }

    /** Every part a case of {@code cases} is taken apart on, each case read once. */
    private static Set<Spelling> partsSplitOn(DecidingCase.Cases cases) {
        Set<Spelling> out = new LinkedHashSet<>();
        cases.fold(new DecidingCase.Cases.Fold<Boolean>() {
            @Override
            public Boolean one(DecidingCase.Cases.One one) {
                out.addAll(WhereEachLineDecides.partsJoinedBy(one.condition()));
                return true;
            }

            @Override
            public Boolean eachOf(DecidingCase.Cases.EachOf node, List<Boolean> alternatives) {
                return true;
            }

            @Override
            public Boolean together(DecidingCase.Cases.Together node, List<Boolean> factors) {
                return true;
            }

            @Override
            public Boolean notTakenApart(DecidingCase.Cases.NotTakenApart notTakenApart) {
                return true;
            }
        });
        return out;
    }

    /** What stands around a step on the way down to it. */
    private sealed interface Frame {}

    /** The {@code ordinal}th application {@code call} makes. */
    private record Applied(ACallOfAnOperation call, ModelOccurrence construct, int ordinal)
            implements Frame {}

    /** Inside the condition of the choice the construct at {@code at} makes. */
    private record Choosing(ConstructOccurrence at, ModelOccurrence construct,
                            CaseExpansion.ChoiceKind kind, int alternatives,
                            Optional<ValueName.Stdlib> operation) implements Frame {}

    /**
     * Where a walk down the derivation stands: the frames around it, outermost first; the choice
     * the step just entered makes, for the step under it to say which of its premises it decides
     * by; the operation whose law the steps below read, until they reach the elements it goes
     * through; and the innermost construct of the model the derivation says a step around it was
     * read at, which wrote the parts made there; and whether the step stands inside some
     * element's statement a quantifier says, which is what its parts are said of.
     */
    private record Context(List<Frame> frames, Optional<Choosing> choosing,
                           Optional<Applied> law, Optional<ModelOccurrence> madeIn,
                           boolean underAQuantifier) {

        static final Context OUTSIDE = new Context(List.of(), Optional.empty(), Optional.empty(),
                Optional.empty(), false);

        Context plain() {
            return choosing.isEmpty() ? this
                    : new Context(frames, Optional.empty(), law, madeIn, underAQuantifier);
        }

        /** Below a quantifier: what is made below is said of the element it chose. */
        Context belowAQuantifier() {
            return new Context(frames, Optional.empty(), law, madeIn, true);
        }

        /**
         * Below a step the derivation says was read at {@code at} — a comparison, or a choice of
         * any kind: what is made below was made there. A construct the model states nothing at,
         * one of the language's own, is inside whichever construct of the model reached it, and
         * that one made what is made below.
         */
        Context readAt(ConstructOccurrence at) {
            Optional<ModelOccurrence> stated = ModelOccurrence.statedAt(at);
            return stated.isEmpty() || stated.equals(madeIn) ? this
                    : new Context(frames, choosing, law, stated, underAQuantifier);
        }

        Context inside(Frame frame) {
            List<Frame> more = new ArrayList<>();
            for (Frame each : frames) {
                // One application inside another of the same call is that inner one.
                if (!(frame instanceof Applied applied && each instanceof Applied around
                        && around.call().equals(applied.call()))) {
                    more.add(each);
                }
            }
            more.add(frame);
            return new Context(List.copyOf(more), Optional.empty(), law, madeIn, underAQuantifier);
        }
    }

    /** Where a part was made: the frames around the step, that step where it writes out the ways
     *  elements are kept, and the construct of the model that made it ({@link Context#madeIn}). */
    private record Origin(List<Frame> frames, Optional<Derivation.WaysWrittenWhenAsked> ways,
                          Optional<ModelOccurrence> madeIn) {}

    private static final class Reading {

        private final Set<Spelling> split;
        private final Map<Spelling, Set<Origin>> made = new LinkedHashMap<>();
        private final Map<Derivation, Set<Context>> seen = new IdentityHashMap<>();
        /** What each kind of factor is first met as, so they are told in the order met. */
        private final Set<Object> order = new LinkedHashSet<>();
        /** Each reading of a helper met, numbered in the order it was first met, which is what the
         *  readings are carried as: a reading is hashed once, where it is met. */
        private final List<ReadingOfAHelper> readings = new ArrayList<>();
        private final Map<ReadingOfAHelper, Integer> numbered = new HashMap<>();
        /** The constructs each reading made its parts at, by its number. */
        private final List<Set<ModelOccurrence>> madeAt = new ArrayList<>();
        /** The readings that made each part, as they are asked for. */
        private final Map<Spelling, BitSet> readingsOf = new HashMap<>();
        private Conclusion concluding;
        private TheWholeNumbersAListStartsWith.Plan plan;
        /** What each conclusion of the derivation being walked comes to put on the elements, by
         *  the conclusion itself: a conclusion a step shares is put once. */
        private Map<Proposition, List<Spelling>> putOn;
        /** Where each statement an element's statement is made of was first concluded, for the
         *  derivation being walked ({@link #whereTheElementsStatementIsMade}). */
        private Map<Spelling, Set<Origin>> ofTheElements;
        /** The steps of the derivation being walked, each once: the ones {@link #concluding}
         *  answers for. */
        private Set<Derivation> inThisRoot;
        /** What {@link #heldUnder} answered, by the step. */
        private Map<Derivation, Set<Spelling>> held;
        private Map<Derivation, Set<Spelling>> under;
        private int steps;

        Reading(Set<Spelling> split) {
            this.split = split;
        }

        /** Whether {@code root} was walked within the steps. */
        boolean from(Derivation root) {
            concluding = new Conclusion(Optional.empty());
            plan = TheWholeNumbersAListStartsWith.planFor(concluding.of(root));
            putOn = new IdentityHashMap<>();
            ofTheElements = new HashMap<>();
            held = new IdentityHashMap<>();
            inThisRoot = Collections.newSetFromMap(new IdentityHashMap<>());
            under = new IdentityHashMap<>();
            boolean walked = visit(root, Context.OUTSIDE);
            if (walked) {
                saidOfTheQuantifiers();
            }
            return walked;
        }

        /** The parts some case is taken apart on that {@code step} concludes. */
        private Set<Spelling> partsUnder(Derivation step) {
            Set<Spelling> known = under.get(step);
            if (known != null) {
                return known;
            }
            Proposition concluded = concluding.concludedAt(step);
            Set<Spelling> out = new HashSet<>();
            if (concluded == null) {
                WrittenLines.premisesOf(step).forEach(each -> out.addAll(partsUnder(each)));
            } else {
                for (Spelling part : WhereEachLineDecides.partsJoinedBy(concluded)) {
                    if (split.contains(part)) {
                        out.add(part);
                    }
                }
                putOnTheElements(concluded, out);
            }
            under.put(step, out);
            return out;
        }

        /**
         * The parts of {@code concluded} as the cases of a comparison over the element of a list
         * of whole numbers take them apart on: with the element put at each of the values the list
         * starts with, the form the comparison's own reading makes of the same statement
         * ({@link TheWholeNumbersAListStartsWith}). On such an element the variable of the loop is
         * gone from a part and a constant is left, and the part is found by making it again of what
         * the step concluded, as the reading of the comparison makes it.
         */
        private void putOnTheElements(Proposition concluded, Set<Spelling> out) {
            out.addAll(putOn.computeIfAbsent(concluded, this::partsPutOn));
        }

        private List<Spelling> partsPutOn(Proposition concluded) {
            if (OnOneElement.theElementOf(concluded).isEmpty()
                    || !(plan.on(concluded) instanceof TheWholeNumbersAListStartsWith.Read.OnEach(
                            var each))) {
                return List.of();
            }
            List<Spelling> out = new ArrayList<>();
            for (TheWholeNumbersAListStartsWith.OnOne one : each) {
                for (Spelling part : WhereEachLineDecides.partsJoinedBy(one.stated())) {
                    if (split.contains(part)) {
                        out.add(part);
                    }
                }
            }
            return out;
        }

        /**
         * Where each statement an element's statement is made of was first concluded, for a step
         * standing inside a quantifier: each part it concludes that no step under it does, and
         * each of them put on the elements as the cases put it ({@link #partsPutOn}). Kept for
         * {@link #saidOfTheQuantifiers}, which tells what the cases made of them.
         */
        private void whereTheElementsStatementIsMade(Derivation step, Context at) {
            Proposition concluded = concluding.concludedAt(step);
            if (concluded == null) {
                return;
            }
            Set<Spelling> below = new HashSet<>();
            WrittenLines.premisesOf(step).forEach(each -> below.addAll(heldUnder(each)));
            Origin origin = new Origin(at.frames(), Optional.empty(), at.madeIn());
            for (Proposition part : WhereEachLineDecides.partsHeldBy(concluded).values()) {
                if (below.contains(part.spelling())) {
                    continue;
                }
                ofTheElements.computeIfAbsent(part.spelling(), _ -> new LinkedHashSet<>())
                        .add(origin);
                for (Proposition put : formsPutOn(part)) {
                    WhereEachLineDecides.partsHeldBy(put).keySet().forEach(spelling ->
                            ofTheElements.computeIfAbsent(spelling, _ -> new LinkedHashSet<>())
                                    .add(origin));
                }
            }
        }

        /**
         * The parts the cases are taken apart on that say some element meets what an element's
         * statement is made of, made where that statement was. What a step concludes of a
         * quantifier is already said as the derivation says it, the denial of the element where it
         * is denied included; the cases take it apart as the lines are read
         * ({@link WhereEachLineDecides#lifted}), each part a quantifier over some of the element's
         * statement. So each is lifted from what the step concluded and made where the statements
         * it is over were: a part is no more than the places its statements were made, and a
         * quantifier over a conjunction is one part made at each of them.
         */
        private void saidOfTheQuantifiers() {
            for (Derivation step : inThisRoot) {
                Proposition concluded = concluding.concludedAt(step);
                if (concluded == null) {
                    continue;
                }
                // A quantifier is said where it is first concluded, and not again by every step
                // above it that holds it.
                Set<Spelling> first = new HashSet<>(heldUnder(step));
                WrittenLines.premisesOf(step).forEach(each -> first.removeAll(heldUnder(each)));
                if (first.isEmpty()) {
                    continue;
                }
                WhereEachLineDecides.partsHeldBy(concluded).forEach((spelling, part) -> {
                    if (first.contains(spelling) && part instanceof Proposition.Some) {
                        for (Proposition form : formsPutOn(part)) {
                            if (form instanceof Proposition.Some some) {
                                saidOfOneQuantifier(some);
                            }
                        }
                    }
                });
            }
        }

        /**
         * The parts the cases make of the quantifier {@code some}: each over some of the
         * statements of its element, so made where those were. A part over statements nothing
         * is known to have made is made by nothing here, and is counted as such.
         */
        private void saidOfOneQuantifier(Proposition.Some some) {
            WhereEachLineDecides.partsHeldBy(WhereEachLineDecides.lifted(some))
                    .forEach((spelling, part) -> {
                        if (!split.contains(spelling) || !(part instanceof Proposition.Some said)) {
                            return;
                        }
                        Set<Origin> there = originsOfTheStatementsOf(said.ofTheElement());
                        if (!there.isEmpty()) {
                            made.computeIfAbsent(spelling, _ -> new LinkedHashSet<>())
                                    .addAll(there);
                        }
                    });
        }

        /** Where each statement {@code element} is made of was first concluded. */
        private Set<Origin> originsOfTheStatementsOf(Proposition element) {
            Set<Origin> out = new LinkedHashSet<>();
            for (Spelling statement : WhereEachLineDecides.partsHeldBy(element).keySet()) {
                Set<Origin> there = ofTheElements.get(statement);
                if (there != null) {
                    out.addAll(there);
                }
            }
            return out;
        }

        /**
         * Every part {@code step} concludes or a step under it does, whether or not a case is
         * taken apart on it: what {@link #partsUnder} answers, without the cases'. A step that
         * concludes nothing of its own holds what its premises do.
         */
        private Set<Spelling> heldUnder(Derivation step) {
            Set<Spelling> known = held.get(step);
            if (known != null) {
                return known;
            }
            Proposition concluded = concluding.concludedAt(step);
            Set<Spelling> out = new HashSet<>();
            if (concluded == null) {
                WrittenLines.premisesOf(step).forEach(each -> out.addAll(heldUnder(each)));
            } else {
                out.addAll(WhereEachLineDecides.partsJoinedBy(concluded));
            }
            held.put(step, out);
            return out;
        }

        /** {@code stated} as it stands, and put on the elements as the cases put it. */
        private List<Proposition> formsPutOn(Proposition stated) {
            List<Proposition> out = new ArrayList<>();
            out.add(stated);
            if (OnOneElement.theElementOf(stated).isPresent()
                    && plan.on(stated) instanceof TheWholeNumbersAListStartsWith.Read.OnEach(
                            var each)) {
                each.forEach(one -> out.add(one.stated()));
            }
            return out;
        }

        private boolean visit(Derivation step, Context at) {
            if (!seen.computeIfAbsent(step, _ -> new HashSet<>()).add(at)) {
                return true;
            }
            if (++steps > STEPS_A_READING_TAKES) {
                return false;
            }
            inThisRoot.add(step);
            Set<Spelling> own = new HashSet<>(partsUnder(step));
            WrittenLines.premisesOf(step).forEach(each -> own.removeAll(partsUnder(each)));
            if (!own.isEmpty()) {
                Origin origin = new Origin(at.frames(),
                        step instanceof Derivation.WaysWrittenWhenAsked ways ? Optional.of(ways)
                                : Optional.empty(), at.madeIn());
                if (origin.ways().isPresent()) {
                    order.add(keptBy(origin.ways().get()));
                }
                own.forEach(part -> made.computeIfAbsent(part, _ -> new LinkedHashSet<>())
                        .add(origin));
            }
            if (at.underAQuantifier()) {
                whereTheElementsStatementIsMade(step, at);
            }
            return switch (step) {
                case Derivation.AnApplication(var call, var ordinal, var derived) ->
                        ModelOccurrence.statedAt(call.at())
                                .map(construct -> visit(derived, at.inside(
                                        registered(new Applied(call, construct, ordinal)))))
                                .orElseGet(() -> visit(derived, at.plain()));
                case Derivation.AChoiceAt(var where, var choice) ->
                        visit(choice, entering(where, choice, at.readAt(where)));
                case Derivation.AComparisonAt(var where, var read) ->
                        visit(read, at.plain().readAt(where));
                case Derivation.IfThenElse(var condition, var then, var otherwise)
                        when at.choosing().isPresent() ->
                        visit(condition, at.inside(at.choosing().get()))
                                && visit(then, at.plain()) && visit(otherwise, at.plain());
                case Derivation.MatchArms(var arms) when at.choosing().isPresent() ->
                        alongTheArms(arms, at);
                case Derivation.AnOperationsCases(var _, var cases)
                        when at.choosing().isPresent() -> alongTheArms(cases, at);
                case Derivation.ASizeInCases(var _, var cases) when at.choosing().isPresent() ->
                        alongTheArms(cases, at);
                case Derivation.OverElementsWrittenOut(var each, var _, var _)
                        when at.law().isPresent() -> overTheElements(each, at);
                case Derivation.SomeElementMeeting(var container, var element, var holds,
                                                   var holdsSomething, var _) -> {
                    Context inside = at.plain().belowAQuantifier();
                    if (!visit(element, inside)) {
                        yield false;
                    }
                    yield holdsSomething.isEmpty() || visit(holdsSomething.get(), at.plain());
                }
                default -> {
                    Context below = at.plain();
                    for (Derivation each : WrittenLines.premisesOf(step)) {
                        if (!visit(each, below)) {
                            yield false;
                        }
                    }
                    yield true;
                }
            };
        }

        private boolean alongTheArms(List<Derivation.MatchArms.Arm> arms, Context at) {
            Context selecting = at.inside(at.choosing().orElseThrow());
            for (Derivation.MatchArms.Arm arm : arms) {
                if (!visit(arm.selects(), selecting) || !visit(arm.states(), at.plain())) {
                    return false;
                }
            }
            return true;
        }

        private boolean overTheElements(List<Derivation> each, Context at) {
            Applied law = at.law().orElseThrow();
            Context below = new Context(at.frames(), Optional.empty(), Optional.empty(),
                    at.madeIn(), at.underAQuantifier());
            for (int ordinal = 0; ordinal < each.size(); ordinal++) {
                if (!visit(each.get(ordinal), below.inside(
                        registered(new Applied(law.call(), law.construct(), ordinal))))) {
                    return false;
                }
            }
            return true;
        }

        /** Where the walk stands below the choice the construct at {@code where} makes. */
        private Context entering(ConstructOccurrence where, Derivation choice, Context at) {
            Optional<ModelOccurrence> construct = ModelOccurrence.statedAt(where);
            if (construct.isEmpty()) {
                return at.plain();
            }
            SourceConstruct written = where.origin().kind();
            Optional<Choosing> choosing = switch (choice) {
                case Derivation.IfThenElse _ when written == SourceConstruct.IF ->
                        Optional.of(new Choosing(where, construct.get(),
                                CaseExpansion.ChoiceKind.IF, 2, Optional.empty()));
                case Derivation.MatchArms(var arms)
                        when written == SourceConstruct.MATCH && arms.size() > 1 ->
                        Optional.of(new Choosing(where, construct.get(),
                                CaseExpansion.ChoiceKind.MATCH, arms.size(), Optional.empty()));
                case Derivation.AnOperationsCases(var operation, var cases)
                        when cases.size() > 1 ->
                        Optional.of(new Choosing(where, construct.get(),
                                CaseExpansion.ChoiceKind.CASES, cases.size(),
                                Optional.of(operation)));
                case Derivation.ASizeInCases(var call, var cases) when cases.size() > 1 ->
                        Optional.of(new Choosing(where, construct.get(),
                                CaseExpansion.ChoiceKind.CASES, cases.size(),
                                Optional.of(call.operation())));
                default -> Optional.empty();
            };
            if (choice instanceof Derivation.ByALaw(var call, var _, var _)) {
                return new Context(at.frames(), Optional.empty(), Optional.of(new Applied(
                        new ACallOfAnOperation(call.operation(), where), construct.get(), 0)),
                        at.madeIn(), at.underAQuantifier());
            }
            choosing.ifPresent(this::registered);
            return new Context(at.frames(), choosing, at.law(), at.madeIn(), at.underAQuantifier());
        }

        private <F extends Frame> F registered(F frame) {
            order.add(keyOf(frame));
            return frame;
        }

        private static Object keyOf(Frame frame) {
            return switch (frame) {
                case Applied applied ->
                        new AppliedBy(applied.construct(), applied.call().operation());
                case Choosing choosing -> new ChosenAt(choosing.construct(), choosing.kind(),
                        choosing.alternatives(), choosing.operation());
            };
        }

        private static KeptBy keptBy(Derivation.WaysWrittenWhenAsked ways) {
            Set<ModelOccurrence> by = new LinkedHashSet<>();
            ways.madeAt().values().forEach(at -> ModelOccurrence.statedAt(at).ifPresent(by::add));
            return new KeptBy(List.copyOf(by));
        }

        /**
         * What made the parts, each thing once, with how many of its occurrences made some.
         *
         * <p>An occurrence is told apart from another of the same thing by the parts it made,
         * and by which application it is: where a walk reads a value made outside a closure again
         * on each application, every reading of it makes the same parts, and they are one
         * occurrence and not as many as the applications. One making a part another makes too
         * makes it all the same; the case is taken apart on a part once.
         */
        CaseExpansion.Attributed attributed(Set<Spelling> ofTheCase, DecidingCase.Cases cases) {
            int unattributed = 0;
            // What each occurrence of each thing made, by where it stood.
            Map<Object, Map<Standing, Set<Spelling>>> occurrences = new LinkedHashMap<>();
            Map<Object, Frame> named = new LinkedHashMap<>();
            Map<PrefixStep, Integer> prefixes = new HashMap<>();
            for (Spelling part : ofTheCase) {
                Set<Origin> from = made.get(part);
                if (from == null) {
                    unattributed++;
                    continue;
                }
                for (Origin origin : from) {
                    int prefix = 0;
                    for (Frame frame : origin.frames()) {
                        prefix = prefixes.computeIfAbsent(new PrefixStep(prefix, frame),
                                _ -> prefixes.size() + 1);
                        Object key = keyOf(frame);
                        named.putIfAbsent(key, frame);
                        occurrences.computeIfAbsent(key, _ -> new LinkedHashMap<>())
                                .computeIfAbsent(new Standing(prefix,
                                        Optional.empty(), frame instanceof Applied applied
                                                ? OptionalInt.of(applied.ordinal())
                                                : OptionalInt.empty()), _ -> new HashSet<>())
                                .add(part);
                    }
                    int whole = prefix;
                    origin.ways().ifPresent(ways -> occurrences
                            .computeIfAbsent(keptBy(ways), _ -> new LinkedHashMap<>())
                            .computeIfAbsent(new Standing(whole, Optional.of(new Identity(ways)),
                                    OptionalInt.empty()), _ -> new HashSet<>())
                            .add(part));
                }
            }
            List<CaseExpansion.Factor> factors = new ArrayList<>();
            for (Object key : order) {
                Map<Standing, Set<Spelling>> met = occurrences.get(key);
                if (met == null) {
                    continue;
                }
                Set<List<Object>> distinct = new HashSet<>();
                met.forEach((where, parts) -> distinct.add(List.of(where.application(), parts)));
                factors.add(switch (key) {
                    case KeptBy by -> new CaseExpansion.KeptWays(by.constructs(),
                            met.values().stream().mapToInt(Set::size).max().orElse(0),
                            distinct.size());
                    default -> switch (named.get(key)) {
                        case Applied applied -> new CaseExpansion.Applications(
                                applied.construct(), applied.call().operation(),
                                distinct.size());
                        case Choosing choosing -> new CaseExpansion.Choice(choosing.construct(),
                                choosing.kind(), choosing.alternatives(), distinct.size(),
                                choosing.operation());
                    };
                });
            }
            return new CaseExpansion.Attributed(factors, ofTheCase.size(), unattributed,
                    multiplied(cases));
        }

        /**
         * The helpers whose readings {@code cases} choose among one beside another
         * ({@link CaseExpansion.MultipliedHelper}, {@link ReadingsChosenOneBesideAnother}).
         */
        private List<CaseExpansion.MultipliedHelper> multiplied(DecidingCase.Cases cases) {
            Map<ValueName.Helper, BitSet> found = ReadingsChosenOneBesideAnother.of(cases,
                    this::readingsMaking, number -> readings.get(number).helper(),
                    (one, other) -> readings.get(one).mayBe(readings.get(other)));
            List<CaseExpansion.MultipliedHelper> out = new ArrayList<>();
            found.forEach((helper, these) -> {
                Set<ModelOccurrence> at = new LinkedHashSet<>();
                these.stream().forEach(each -> at.addAll(madeAt.get(each)));
                out.add(new CaseExpansion.MultipliedHelper(helper, List.copyOf(at)));
            });
            return out;
        }

        /**
         * The readings of helpers that made {@code part}: for each place it was made inside a
         * construct a helper's body wrote ({@link Context#madeIn}), standing in a copy of
         * that body, the copy and the applications around it made outside the copy.
         *
         * <p>The helper the innermost copy is of is the one that wrote it: a construct of the model
         * stands in the copies of whoever wrote it, out of any block handed over
         * ({@link ModelOccurrence#statedAt}). One the language writes is no author's to declare.
         *
         * <p>And the most a walk said of where each was made. A part made on an application is
         * made in that copy on that application, and a walk of a derivation that went past the
         * application without saying so finds it in the copy alone; that is the same reading said
         * with less, and not another one, so a reading of a copy on fewer of the applications
         * another reading of the same copy that made the part is on is left out.
         */
        private BitSet readingsMaking(Spelling part) {
            BitSet known = readingsOf.get(part);
            if (known != null) {
                return known;
            }
            Map<ReadingOfAHelper, Set<ModelOccurrence>> making = new LinkedHashMap<>();
            for (Origin origin : made.getOrDefault(part, Set.of())) {
                if (origin.madeIn().isEmpty()) {
                    continue;
                }
                ModelOccurrence written = origin.madeIn().get();
                if (!(written.lineage() instanceof ExpansionLineage.Expansion copy)
                        || !(copy.expanded() instanceof ValueName.Helper helper)
                        || helper.isDeclaredByLanguage()) {
                    continue;
                }
                List<Applied> on = new ArrayList<>();
                for (Frame frame : origin.frames()) {
                    if (frame instanceof Applied applied
                            && !standsIn(applied.construct().lineage(), copy)) {
                        on.add(applied);
                    }
                }
                making.computeIfAbsent(new ReadingOfAHelper(helper, copy, List.copyOf(on)),
                        _ -> new LinkedHashSet<>()).add(written);
            }
            BitSet out = new BitSet();
            making.forEach((reading, at) -> {
                if (making.keySet().stream().anyMatch(more -> more.saysMoreThan(reading))) {
                    return;
                }
                int number = numbered.computeIfAbsent(reading, made -> {
                    readings.add(made);
                    madeAt.add(new LinkedHashSet<>());
                    return readings.size() - 1;
                });
                out.set(number);
                madeAt.get(number).addAll(at);
            });
            readingsOf.put(part, out);
            return out;
        }

        /** Whether {@code lineage} is {@code copy} or a copy made inside it. */
        private static boolean standsIn(ExpansionLineage lineage, ExpansionLineage.Expansion copy) {
            for (ExpansionLineage each = lineage; each instanceof ExpansionLineage.Expansion step;
                    each = step.within()) {
                if (step.equals(copy)) {
                    return true;
                }
            }
            return false;
        }
    }

    /**
     * One reading of a helper's body: the copy of it, and the applications made outside the copy
     * it was read on. Two readings are two answers a behavior would give.
     */
    private record ReadingOfAHelper(ValueName.Helper helper, ExpansionLineage.Expansion copy,
                                    List<Applied> on) {

        /** Whether this is {@code other}'s copy on every application {@code other} is on and on
         *  more besides: the same reading, said with more of where it was made. */
        boolean saysMoreThan(ReadingOfAHelper other) {
            return copy.equals(other.copy()) && on.size() > other.on().size()
                    && on.containsAll(other.on());
        }

        /** Whether this and {@code other} may be one reading: the same, or one of them the other
         *  said with less. */
        boolean mayBe(ReadingOfAHelper other) {
            return equals(other) || saysMoreThan(other) || other.saysMoreThan(this);
        }
    }

    /**
     * Where one occurrence of a thing stood: the frames down to it, the writing out of kept ways
     * it is where it is one, and which application of its call it is where it is an application.
     *
     * @param frames the frames down to it, as the number {@link PrefixStep} gives them: frames
     *               alike are one number however many origins stand in them
     */
    private record Standing(int frames, Optional<Identity> writing, OptionalInt application) {}

    /**
     * One more frame below the frames numbered {@code before}, nought for none: what numbers the
     * frames an occurrence stood in one frame at a time, so that frames alike are told alike
     * without each being written out and compared again for every frame below it.
     */
    private record PrefixStep(int before, Frame frame) {}

    /** Applications of closures by calls of {@code operation} at {@code construct}. */
    private record AppliedBy(ModelOccurrence construct, ValueName.Stdlib operation) {}

    /** Choosings at {@code construct}. */
    private record ChosenAt(ModelOccurrence construct, CaseExpansion.ChoiceKind kind,
                            int alternatives, Optional<ValueName.Stdlib> operation) {}

    /** Writings out of the ways elements are kept by the truths at {@code constructs}. */
    private record KeptBy(List<ModelOccurrence> constructs) {}

    /** A step, told apart from every other by being itself. */
    private record Identity(Object of) {

        @Override
        public boolean equals(Object other) {
            return other instanceof Identity identity && identity.of == of;
        }

        @Override
        public int hashCode() {
            return System.identityHashCode(of);
        }
    }
}
