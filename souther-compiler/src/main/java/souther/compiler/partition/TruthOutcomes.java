package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.UnaryOperator;

/**
 * Which answers a truth can give, and whether a container can be empty — as far as what the
 * source wrote says.
 *
 * <p>Asked of what an operation answers, where the tree's own reading has no word: a truth an
 * operation answers, and whether what an operation leaves holds anything. The operations the
 * library says the answer turns on a closure for are read by what they do with it — some element,
 * every element, the elements kept — so a closure fixed at one answer carries that answer through:
 * {@code List.all(_ -> true, xs)} is true whatever {@code xs} is, and {@code List.any(_ -> true,
 * xs)} is whether {@code xs} holds anything.
 *
 * <p>Five answers and not two ({@link Outcomes}). A value the same whatever the input gives one
 * answer, and which one is a second question this can answer for some values and not others; and
 * whether it is the same whatever the input is a third, which a value made of one this cannot name
 * and one that varies cannot always answer.
 */
final class TruthOutcomes {

    private TruthOutcomes() {
    }

    /**
     * Which answers something can give, as far as this reading can say.
     *
     * <p>Of a truth, true and false. Of whether a container is empty, true is empty.
     */
    enum Outcomes {
        /** It may come out either way. */
        EITHER,
        /** It comes out true and never false. */
        ONLY_TRUE,
        /** It comes out false and never true. */
        ONLY_FALSE,
        /**
         * It comes out one way whatever the input, and which one this reading cannot say.
         *
         * <p>No way is stood behind, which is what the tree's own reading answers of a value it
         * cannot witness: the way through it is kept as one, and nothing is claimed of either.
         */
        FIXED_UNNAMED,
        /**
         * This reading cannot say even whether it is the same whatever the input.
         *
         * <p>A value made of one fixed at an answer nobody named and one that varies: which of the
         * two decides it is the answer nobody named. No way is stood behind, as above, and it is
         * not taken for fixed.
         */
        UNKNOWN;

        /** Whether some input brings it out {@code want}, as far as this reading stands behind. */
        boolean allows(boolean want) {
            return switch (this) {
                case EITHER -> true;
                case ONLY_TRUE -> want;
                case ONLY_FALSE -> !want;
                case FIXED_UNNAMED, UNKNOWN -> false;
            };
        }

        /** Whether it is the same whatever the input. */
        boolean isFixed() {
            return switch (this) {
                case ONLY_TRUE, ONLY_FALSE, FIXED_UNNAMED -> true;
                case EITHER, UNKNOWN -> false;
            };
        }

        Outcomes denied() {
            return switch (this) {
                case ONLY_TRUE -> ONLY_FALSE;
                case ONLY_FALSE -> ONLY_TRUE;
                case EITHER, FIXED_UNNAMED, UNKNOWN -> this;
            };
        }

        static Outcomes only(boolean value) {
            return value ? ONLY_TRUE : ONLY_FALSE;
        }

        /**
         * Both holding.
         *
         * <p>Either part failing settles it, and one that always holds leaves the other. Two that
         * vary vary together and two fixed are fixed; one fixed at an answer nobody named beside
         * one that varies is either, or false, by the answer nobody named.
         */
        Outcomes and(Outcomes other) {
            if (this == ONLY_FALSE || other == ONLY_FALSE) {
                return ONLY_FALSE;
            }
            if (this == ONLY_TRUE) {
                return other;
            }
            if (other == ONLY_TRUE) {
                return this;
            }
            if (this == other && this != UNKNOWN) {
                return this;
            }
            return UNKNOWN;
        }

        /** Either holding. */
        Outcomes or(Outcomes other) {
            return denied().and(other.denied()).denied();
        }
    }

    /**
     * Which answers {@code truth} can give.
     *
     * @param denotes what a name stands for, where something outside the value says
     * @param symbols the library the checker folds against, or null where nothing is folded
     */
    static Outcomes ofTheTruth(Core truth, UnaryOperator<Core> denotes, Symbols symbols) {
        return new Reading(denotes, symbols).truth(truth, Scope.OUTSIDE);
    }

    /**
     * What {@code application}'s side {@code aspect} comes to — its truth, or whether what it
     * answers is empty.
     */
    static Outcomes ofTheSide(Core application, AnswerAspect aspect, UnaryOperator<Core> denotes,
                              Symbols symbols) {
        Reading reading = new Reading(denotes, symbols);
        return switch (aspect) {
            case TRUTH -> reading.truth(application, Scope.OUTSIDE);
            case EMPTINESS -> reading.emptiness(application, Scope.OUTSIDE);
        };
    }

    /**
     * Whether {@code e} is a value the source wrote out all the way down — a written value, and
     * every part of one built out of written values.
     *
     * <p>Which is a value the same every time. A list is written out only where every element is:
     * a list holding a position is a list of that position's values.
     */
    static boolean wholeValueWrittenOut(Core standing, UnaryOperator<Core> denotes) {
        return wholeValueWrittenOut(standing, denotes, Set.of());
    }

    /**
     * The same, with each of {@code written} standing for a written value nobody gave — what a
     * predicate is handed from a container written out.
     */
    private static boolean wholeValueWrittenOut(Core standing, UnaryOperator<Core> denotes,
                                                Set<BindingId> written) {
        return switch (Core.withoutStanding(standing)) {
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _,
                 Core.UnitValue _, Core.OptionNone _ -> true;
            case Core.Read name -> written.contains(name.binding());
            case Core.Neg negated ->
                    wholeValueWrittenOut(denotes.apply(negated.operand()), denotes, written);
            case Core.OptionSome some ->
                    wholeValueWrittenOut(denotes.apply(some.value()), denotes, written);
            case Core.ListLit list -> list.elements().stream()
                    .allMatch(each -> wholeValueWrittenOut(denotes.apply(each), denotes, written));
            case Core.Tuple tuple -> tuple.elements().stream()
                    .allMatch(each -> wholeValueWrittenOut(denotes.apply(each), denotes, written));
            case Core.Construct made -> made.values().stream()
                    .allMatch(each -> wholeValueWrittenOut(denotes.apply(each.value()), denotes,
                            written));
            case null, default -> false;
        };
    }

    /**
     * The bindings met inside the value: what a {@code let} binds, and which names stand for a
     * written value without one being given.
     *
     * <p>A binding the library writes — a denial binds what it denies — is one the reading
     * outside the value has not got, so these are asked before it.
     */
    private record Scope(Map<BindingId, Core> bound, Set<BindingId> written) {

        static final Scope OUTSIDE = new Scope(Map.of(), Set.of());

        Scope with(Core.LetIn let) {
            Map<BindingId, Core> out = new HashMap<>(bound);
            out.put(let.binder().binding(), let.value());
            return new Scope(out, written);
        }

        /** With what {@code block} is handed standing for written values. */
        Scope handingWrittenValuesTo(Core.Block block) {
            Set<BindingId> out = new HashSet<>(written);
            block.params().forEach(each -> out.add(each.binding()));
            return new Scope(bound, out);
        }
    }

    /**
     * One reading, over the tree where the language's operations stand — so an application of
     * one is read for what the library says it does, and never handed to a reading of the tree
     * that runs, which has no such node.
     */
    private record Reading(UnaryOperator<Core> denotes, Symbols symbols) {

        Outcomes truth(Core standing, Scope scope) {
            Core e = Core.withoutStanding(standing);
            switch (e) {
                case Core.Bool written -> {
                    return Outcomes.only(written.value());
                }
                case Core.LetIn let -> {
                    return truth(let.body(), scope.with(let));
                }
                case Core.Read name -> {
                    Core value = valueOf(name, scope);
                    return value != null ? truth(value, scope) : unsaid(name, scope);
                }
                default -> { }
            }
            Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, true);
            if (denied.isPresent()) {
                Outcomes under = truth(denied.get().part(), scope);
                return denied.get().positive() ? under : under.denied();
            }
            if (e instanceof Core.Binary binary) {
                Optional<ConditionJoin> joined = ConditionJoin.of(binary.op());
                if (joined.isPresent()) {
                    Outcomes left = truth(binary.left(), scope);
                    Outcomes right = truth(binary.right(), scope);
                    return joined.get().under(true) == ConditionJoin.BOTH
                            ? left.and(right) : left.or(right);
                }
                return folded(e).orElseGet(() -> writtenOut(binary.left(), scope)
                        && writtenOut(binary.right(), scope)
                        ? Outcomes.FIXED_UNNAMED : Outcomes.EITHER);
            }
            if (!(e instanceof Core.PreservedCall applied)) {
                return Outcomes.EITHER;
            }
            ValueName operation = applied.declared().operation();
            var facts = DefaultBoundOperationFacts.get();
            if (facts.meansTheSameAsASizeOfNought(operation) != null
                    && applied.args().size() == 1) {
                return emptiness(applied.args().getFirst(), scope);
            }
            Outcomes quantified = quantified(applied, scope);
            if (quantified != null) {
                return quantified;
            }
            Optional<Outcomes> folded = folded(e);
            if (folded.isPresent()) {
                return folded.get();
            }
            return everyArgumentWrittenOut(applied, scope) ? Outcomes.FIXED_UNNAMED
                    : Outcomes.EITHER;
        }

        /** Whether what {@code standing} comes to is empty: true is empty. */
        Outcomes emptiness(Core standing, Scope scope) {
            Core e = Core.withoutStanding(standing);
            switch (e) {
                case Core.LetIn let -> {
                    return emptiness(let.body(), scope.with(let));
                }
                case Core.Read name -> {
                    Core value = valueOf(name, scope);
                    return value != null ? emptiness(value, scope) : unsaid(name, scope);
                }
                case Core.ListLit list -> {
                    return Outcomes.only(list.elements().isEmpty());
                }
                case Core.Str text -> {
                    return Outcomes.only(text.value().isEmpty());
                }
                default -> { }
            }
            if (!(e instanceof Core.PreservedCall applied)) {
                return Outcomes.EITHER;
            }
            var facts = DefaultBoundOperationFacts.get();
            ValueName operation = applied.declared().operation();
            var turns = facts.turnsOnWhetherAnArgumentHolds(operation, AnswerAspect.EMPTINESS);
            Core.Block kept = turns == null ? null
                    : closure(applied.args().get(turns.argument().position()), scope);
            Integer handed = keptFrom(operation);
            if (kept == null || handed == null) {
                return everyArgumentWrittenOut(applied, scope) ? Outcomes.FIXED_UNNAMED
                        : Outcomes.EITHER;
            }
            // What is kept is what the closure holds of, out of what it was handed: kept by a
            // closure holding of nothing, nothing is, and that is the same as no element of what
            // it was handed meeting the closure.
            return some(applied.args().get(handed), kept, scope, false).denied();
        }

        /**
         * Which argument {@code operation} keeps elements of, where what it answers is elements of
         * one argument's own — or null where the library says nothing of the kind.
         */
        private static Integer keptFrom(ValueName operation) {
            var built = DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
            return built != null && built.outputs().size() == 1
                    && built.lineage() instanceof ElementLineage.SameAs<DeclaredArgument>(var source)
                    ? source.argument().position() : null;
        }

        /**
         * What a predicate asked of some element, or of every element, comes to — or null where
         * {@code applied} asks none.
         *
         * <p>Some element meets a predicate where the container holds one and the predicate can
         * hold; every element does where the container holds none or the predicate cannot fail.
         * So a predicate fixed false makes some element meeting it false, and one fixed true makes
         * every element meeting it true, whatever the container — and the other way round, what
         * is left is whether the container holds anything.
         */
        private Outcomes quantified(Core.PreservedCall applied, Scope scope) {
            var facts = DefaultBoundOperationFacts.get();
            ValueName operation = applied.declared().operation();
            var container = facts.readsItsContainer(operation);
            var turns = facts.turnsOnWhetherAnArgumentHolds(operation, AnswerAspect.TRUTH);
            if (container == null || turns == null) {
                return null;
            }
            Core.Block predicate = closure(applied.args().get(turns.argument().position()), scope);
            if (predicate == null) {
                return null;
            }
            Core handed = applied.args().get(container.container().position());
            // Every element meeting p is no element failing it, which is some element meeting its
            // denial denied — so one rule answers both.
            return facts.statesItsPredicateOfEveryElement(operation)
                    ? some(handed, predicate, scope, true).denied()
                    : some(handed, predicate, scope, false);
        }

        /**
         * Some element of {@code container} meeting {@code predicate} — or failing it, where
         * {@code failing} — from what each can give.
         *
         * <p>None where the container holds none or no element can meet it; whether the container
         * holds anything where every element does. What the predicate is handed is an element of
         * the container, so over a container written out it is a written value, and the
         * predicate is read with it standing for one: what it answers is then the same every time
         * exactly where nothing else it reads varies, however it differs from one element to the
         * next.
         */
        private Outcomes some(Core container, Core.Block predicate, Scope scope,
                              boolean failing) {
            Scope inside = writtenOut(container, scope)
                    ? scope.handingWrittenValuesTo(predicate) : scope;
            Outcomes each = truth(predicate.body(), inside);
            if (failing) {
                each = each.denied();
            }
            Outcomes empty = emptiness(container, scope);
            // A container holding none has no element meeting anything.
            if (empty == Outcomes.ONLY_TRUE) {
                return Outcomes.ONLY_FALSE;
            }
            return switch (each) {
                case ONLY_FALSE -> Outcomes.ONLY_FALSE;
                // Every element meets it, so some does exactly where there is one.
                case ONLY_TRUE -> empty.denied();
                // Each meeting it or not, beside a container that may hold one: what a container
                // that holds one comes to is what its elements do, and an empty one is none.
                case EITHER -> empty == Outcomes.ONLY_FALSE || empty == Outcomes.EITHER
                        ? Outcomes.EITHER : Outcomes.UNKNOWN;
                case FIXED_UNNAMED -> empty == Outcomes.ONLY_FALSE
                        || empty == Outcomes.FIXED_UNNAMED
                        ? Outcomes.FIXED_UNNAMED : Outcomes.UNKNOWN;
                case UNKNOWN -> Outcomes.UNKNOWN;
            };
        }

        private Core.Block closure(Core handed, Scope scope) {
            Core e = Core.withoutStanding(handed);
            if (e instanceof Core.Read name) {
                Core value = valueOf(name, scope);
                e = value == null ? e : Core.withoutStanding(value);
            }
            return e instanceof Core.Block block ? block : null;
        }

        private Optional<Outcomes> folded(Core e) {
            return symbols == null ? Optional.empty()
                    : BooleanMeaning.folded(e, symbols).map(Outcomes::only);
        }

        private boolean everyArgumentWrittenOut(Core.PreservedCall applied, Scope scope) {
            return applied.args().stream().allMatch(each -> writtenOut(each, scope));
        }

        /** Whether {@code standing} is a value written out, with the names in it read here. */
        private boolean writtenOut(Core standing, Scope scope) {
            UnaryOperator<Core> here = one -> resolved(one, scope);
            return wholeValueWrittenOut(here.apply(standing), here, scope.written());
        }

        /** What {@code one} stands for here, or itself where it is a name nothing gives. */
        private Core resolved(Core one, Scope scope) {
            if (!(Core.withoutStanding(one) instanceof Core.Read name)) {
                return denotes.apply(one);
            }
            Core value = valueOf(name, scope);
            return value == null ? one : value;
        }

        /**
         * What a name nothing gives a value for comes to: the same every time where it stands for
         * a written value, and either otherwise.
         */
        private static Outcomes unsaid(Core.Read name, Scope scope) {
            return scope.written().contains(name.binding()) ? Outcomes.FIXED_UNNAMED
                    : Outcomes.EITHER;
        }

        /** What {@code name} stands for, or null where nothing says. */
        private Core valueOf(Core.Read name, Scope scope) {
            Core here = scope.bound().get(name.binding());
            if (here != null) {
                return here;
            }
            Core denoted = denotes.apply(name);
            return Core.withoutStanding(denoted) instanceof Core.Read same
                    && same.binding().equals(name.binding()) ? null : denoted;
        }
    }
}
