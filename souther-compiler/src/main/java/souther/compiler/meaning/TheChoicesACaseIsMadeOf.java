package souther.compiler.meaning;

import souther.compiler.types.ACallOfAnOperation;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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
        List<Set<Spelling>> each = cases.stream().map(TheChoicesACaseIsMadeOf::partsSplitOn)
                .toList();
        CaseExpansion.Attribution given = derivedBy.isEmpty()
                ? new CaseExpansion.NotAttributed(CaseExpansion.WhyNotAttributed.NOTHING_DERIVED)
                : null;
        Set<Spelling> any = new HashSet<>();
        each.forEach(any::addAll);
        Reading reading = new Reading(any);
        for (Derivation one : derivedBy) {
            if (given == null && !reading.from(one)) {
                given = new CaseExpansion.NotAttributed(
                        CaseExpansion.WhyNotAttributed.STEPS_A_READING_TAKES);
            }
        }
        List<CaseExpansion.Attribution> out = new ArrayList<>();
        for (Set<Spelling> split : each) {
            out.add(given != null ? given : reading.attributed(split));
        }
        return out;
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
                            Optional<ValueName> operation) implements Frame {}

    /**
     * Where a walk down the derivation stands: the frames around it, outermost first; the choice
     * the step just entered makes, for the step under it to say which of its premises it decides
     * by; and the operation whose law the steps below read, until they reach the elements it goes
     * through.
     */
    private record Context(List<Frame> frames, Optional<Choosing> choosing,
                           Optional<Applied> law) {

        static final Context OUTSIDE = new Context(List.of(), Optional.empty(), Optional.empty());

        Context plain() {
            return choosing.isEmpty() ? this : new Context(frames, Optional.empty(), law);
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
            return new Context(List.copyOf(more), Optional.empty(), law);
        }
    }

    /** Where a part was made: the frames around the step, and that step where it writes out
     *  the ways elements are kept. */
    private record Origin(List<Frame> frames, Optional<Derivation.WaysWrittenWhenAsked> ways) {}

    private static final class Reading {

        private final Set<Spelling> split;
        private final Map<Spelling, Set<Origin>> made = new LinkedHashMap<>();
        private final Map<Derivation, Set<Context>> seen = new IdentityHashMap<>();
        /** What each kind of factor is first met as, so they are told in the order met. */
        private final Set<Object> order = new LinkedHashSet<>();
        private Conclusion concluding;
        private Map<Derivation, Set<Spelling>> under;
        private int steps;

        Reading(Set<Spelling> split) {
            this.split = split;
        }

        /** Whether {@code root} was walked within the steps. */
        boolean from(Derivation root) {
            concluding = new Conclusion(Optional.empty());
            concluding.of(root);
            under = new IdentityHashMap<>();
            return visit(root, Context.OUTSIDE);
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
            }
            under.put(step, out);
            return out;
        }

        private boolean visit(Derivation step, Context at) {
            if (!seen.computeIfAbsent(step, _ -> new HashSet<>()).add(at)) {
                return true;
            }
            if (++steps > STEPS_A_READING_TAKES) {
                return false;
            }
            Set<Spelling> own = new HashSet<>(partsUnder(step));
            WrittenLines.premisesOf(step).forEach(each -> own.removeAll(partsUnder(each)));
            if (!own.isEmpty()) {
                Origin origin = new Origin(at.frames(),
                        step instanceof Derivation.WaysWrittenWhenAsked ways ? Optional.of(ways)
                                : Optional.empty());
                if (origin.ways().isPresent()) {
                    order.add(keptBy(origin.ways().get()));
                }
                own.forEach(part -> made.computeIfAbsent(part, _ -> new LinkedHashSet<>())
                        .add(origin));
            }
            return switch (step) {
                case Derivation.AnApplication(var call, var ordinal, var derived) ->
                        ModelOccurrence.statedAt(call.at())
                                .map(construct -> visit(derived, at.inside(
                                        registered(new Applied(call, construct, ordinal)))))
                                .orElseGet(() -> visit(derived, at.plain()));
                case Derivation.AChoiceAt(var where, var choice) ->
                        visit(choice, entering(where, choice, at));
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
            Context below = new Context(at.frames(), Optional.empty(), Optional.empty());
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
                        new ACallOfAnOperation(call.operation(), where), construct.get(), 0)));
            }
            choosing.ifPresent(this::registered);
            return new Context(at.frames(), choosing, at.law());
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
        CaseExpansion.Attributed attributed(Set<Spelling> ofTheCase) {
            int unattributed = 0;
            // What each occurrence of each thing made, by where it stood.
            Map<Object, Map<Object, Set<Spelling>>> occurrences = new LinkedHashMap<>();
            Map<Object, Frame> named = new LinkedHashMap<>();
            for (Spelling part : ofTheCase) {
                Set<Origin> from = made.get(part);
                if (from == null) {
                    unattributed++;
                    continue;
                }
                for (Origin origin : from) {
                    List<Frame> frames = origin.frames();
                    for (int at = 0; at < frames.size(); at++) {
                        Object key = keyOf(frames.get(at));
                        named.putIfAbsent(key, frames.get(at));
                        occurrences.computeIfAbsent(key, _ -> new LinkedHashMap<>())
                                .computeIfAbsent(List.copyOf(frames.subList(0, at + 1)),
                                        _ -> new HashSet<>())
                                .add(part);
                    }
                    origin.ways().ifPresent(ways -> occurrences
                            .computeIfAbsent(keptBy(ways), _ -> new LinkedHashMap<>())
                            .computeIfAbsent(List.of(new Identity(ways), frames),
                                    _ -> new HashSet<>())
                            .add(part));
                }
            }
            List<CaseExpansion.Factor> factors = new ArrayList<>();
            for (Object key : order) {
                Map<Object, Set<Spelling>> met = occurrences.get(key);
                if (met == null) {
                    continue;
                }
                Set<Object> distinct = new HashSet<>();
                met.forEach((where, parts) -> distinct.add(List.of(which(where), parts)));
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
            return new CaseExpansion.Attributed(factors, ofTheCase.size(), unattributed);
        }

        /** Which application an occurrence standing at {@code where} is, where it is one: the
         *  ordinal of the innermost frame, or nothing that tells it apart. */
        private static Object which(Object where) {
            return where instanceof List<?> frames && !frames.isEmpty()
                    && frames.getLast() instanceof Applied applied ? applied.ordinal() : "";
        }
    }

    /** Applications of closures by calls of {@code operation} at {@code construct}. */
    private record AppliedBy(ModelOccurrence construct, ValueName operation) {}

    /** Choosings at {@code construct}. */
    private record ChosenAt(ModelOccurrence construct, CaseExpansion.ChoiceKind kind,
                            int alternatives, Optional<ValueName> operation) {}

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
