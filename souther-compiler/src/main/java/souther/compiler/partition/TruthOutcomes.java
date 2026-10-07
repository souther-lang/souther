package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.DeclaredArgument;
import souther.compiler.check.DefaultBoundOperationFacts;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.ConditionJoin;
import souther.compiler.semantics.ElementLineage;
import souther.compiler.types.ValueName;

import java.util.Optional;

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
 *
 * <p>Read over the tree where the language's operations stand, so an application of one is read
 * for what the library says it does and never handed to a reading of the tree that runs, which
 * has no such node. What the names in it stand for is the reading of the input's answer
 * ({@link WhatNamesStandFor}), and nothing here keeps an account of its own: a closure handed the
 * elements of a list written out is handed written values because that reading says so, wherever
 * the closure is read from.
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

        /** Whether it comes out {@code value} for every input, which this reading can say. */
        boolean always(boolean value) {
            return this == only(value);
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
     * @param names   what the names in it stand for
     * @param symbols the library the checker folds against, or null where nothing is folded
     */
    static Outcomes ofTheTruth(Core truth, WhatNamesStandFor names, Symbols symbols) {
        return new Reading(names, symbols).truth(truth);
    }

    /**
     * What {@code application}'s side {@code aspect} comes to — its truth, or whether what it
     * answers is empty.
     */
    static Outcomes ofTheSide(Core application, AnswerAspect aspect, WhatNamesStandFor names,
                              Symbols symbols) {
        Reading reading = new Reading(names, symbols);
        return switch (aspect) {
            case TRUTH -> reading.truth(application);
            case EMPTINESS -> reading.emptiness(application);
        };
    }

    /**
     * One reading of the tree, in the names {@code names} holds where it stands.
     *
     * <p>Stepped with the walk: what is under a {@code let} or a closure, or what a name stands for,
     * is read where it stands, which binds names this one does not.
     */
    private record Reading(WhatNamesStandFor names, Symbols symbols) {

        private Reading in(WhatNamesStandFor other) {
            return other == names ? this : new Reading(other, symbols);
        }

        private Reading at(Denotation where) {
            return in(names.in(where.at()));
        }

        Outcomes truth(Core standing) {
            Core e = Core.withoutStanding(standing);
            switch (e) {
                case Core.Bool written -> {
                    return Outcomes.only(written.value());
                }
                case Core.LetIn let -> {
                    return in(names.entering(new ScopeStep.Let(let))).truth(let.body());
                }
                case Core.Read name -> {
                    Denotation value = valueOf(name);
                    return value != null ? at(value).truth(value.value()) : unsaid(name);
                }
                default -> { }
            }
            Optional<BooleanMeaning.UnderADenial> denied = BooleanMeaning.underADenial(e, true);
            if (denied.isPresent()) {
                Outcomes under = truth(denied.get().part());
                return denied.get().positive() ? under : under.denied();
            }
            if (e instanceof Core.Binary binary) {
                Optional<ConditionJoin> joined = ConditionJoin.of(binary.op());
                if (joined.isPresent()) {
                    Outcomes left = truth(binary.left());
                    Outcomes right = truth(binary.right());
                    return joined.get().under(true) == ConditionJoin.BOTH
                            ? left.and(right) : left.or(right);
                }
                Optional<Boolean> everyRow = names.everyRowBrings(e);
                if (everyRow.isPresent()) {
                    return Outcomes.only(everyRow.get());
                }
                return folded(e).orElseGet(() -> names.writtenOut(binary.left())
                        && names.writtenOut(binary.right())
                        ? Outcomes.FIXED_UNNAMED : Outcomes.EITHER);
            }
            AnOperationApplied applied = AnOperationApplied.of(e);
            if (applied == null) {
                return Outcomes.EITHER;
            }
            var facts = DefaultBoundOperationFacts.get();
            if (facts.meansTheSameAsASizeOfNought(applied.operation()) != null
                    && applied.args().size() == 1) {
                return emptiness(applied.args().getFirst());
            }
            Outcomes quantified = quantified(applied);
            if (quantified != null) {
                return quantified;
            }
            Optional<Outcomes> folded = folded(e);
            if (folded.isPresent()) {
                return folded.get();
            }
            return everyArgumentWrittenOut(applied) ? Outcomes.FIXED_UNNAMED : Outcomes.EITHER;
        }

        /** Whether what {@code standing} comes to is empty: true is empty. */
        Outcomes emptiness(Core standing) {
            Core e = Core.withoutStanding(standing);
            switch (e) {
                case Core.LetIn let -> {
                    return in(names.entering(new ScopeStep.Let(let))).emptiness(let.body());
                }
                case Core.Read name -> {
                    Denotation value = valueOf(name);
                    return value != null ? at(value).emptiness(value.value()) : unsaid(name);
                }
                case Core.ListLit list -> {
                    return Outcomes.only(list.elements().isEmpty());
                }
                case Core.Str text -> {
                    return Outcomes.only(text.value().isEmpty());
                }
                default -> { }
            }
            AnOperationApplied applied = AnOperationApplied.of(e);
            if (applied == null) {
                return Outcomes.EITHER;
            }
            var facts = DefaultBoundOperationFacts.get();
            var turns = facts.turnsOnWhetherAnArgumentHolds(applied.operation(),
                    AnswerAspect.EMPTINESS);
            Denotation kept = turns == null ? null : closure(applied.argument(turns.argument()));
            DeclaredArgument from = keptFrom(applied.operation());
            Core handed = from == null ? null : applied.argument(from);
            if (kept == null || handed == null) {
                return everyArgumentWrittenOut(applied) ? Outcomes.FIXED_UNNAMED
                        : Outcomes.EITHER;
            }
            // What is kept is what the closure holds of, out of what it was handed: kept by a
            // closure holding of nothing, nothing is, and that is the same as no element of what
            // it was handed meeting the closure.
            return some(handed, kept, false).denied();
        }

        /**
         * Which argument {@code operation} keeps elements of, where what it answers is elements of
         * one argument's own — or null where the library says nothing of the kind.
         */
        private static DeclaredArgument keptFrom(ValueName operation) {
            var built = DefaultBoundOperationFacts.get().buildsItsResultFrom(operation);
            return built != null && built.outputs().size() == 1
                    && built.lineage() instanceof ElementLineage.SameAs<DeclaredArgument>(var source)
                    ? source.argument() : null;
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
        private Outcomes quantified(AnOperationApplied applied) {
            var facts = DefaultBoundOperationFacts.get();
            ValueName operation = applied.operation();
            var container = facts.readsItsContainer(operation);
            var turns = facts.turnsOnWhetherAnArgumentHolds(operation, AnswerAspect.TRUTH);
            if (container == null || turns == null) {
                return null;
            }
            Denotation predicate = closure(applied.argument(turns.argument()));
            Core handed = applied.argument(container.container());
            if (predicate == null || handed == null) {
                return null;
            }
            // Every element meeting p is no element failing it, which is some element meeting its
            // denial denied — so one rule answers both.
            return facts.statesItsPredicateOfEveryElement(operation)
                    ? some(handed, predicate, true).denied()
                    : some(handed, predicate, false);
        }

        /**
         * Some element of {@code container} meeting {@code predicate} — or failing it, where
         * {@code failing} — from what each can give.
         *
         * <p>None where the container holds none or no element can meet it; whether the container
         * holds anything where every element does. What the predicate is handed over a container
         * written out is one of its written values, so what it answers there is the same every
         * time exactly where nothing else it reads varies, however it differs from one element to
         * the next — which is the predicate's own truth, read with its names as they stand.
         *
         * @param predicate what the predicate answers with, where it stands
         */
        private Outcomes some(Core container, Denotation predicate, boolean failing) {
            Outcomes each = at(predicate).truth(predicate.value());
            if (failing) {
                each = each.denied();
            }
            Outcomes empty = emptiness(container);
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

        /** What the closure {@code handed} answers with, read inside it — or null where it stands
         *  for no closure. */
        private Denotation closure(Core handed) {
            if (handed == null) {
                return null;
            }
            Denotation stands = names.denotes(handed);
            return Core.withoutStanding(stands.value()) instanceof Core.Block block
                    ? new Denotation(block.body(), stands.at()) : null;
        }

        private Optional<Outcomes> folded(Core e) {
            return symbols == null ? Optional.empty()
                    : BooleanMeaning.folded(e, symbols).map(Outcomes::only);
        }

        private boolean everyArgumentWrittenOut(AnOperationApplied applied) {
            return applied.args().stream().allMatch(names::writtenOut);
        }

        /**
         * What a name nothing gives one value for comes to: the same every time where it stands
         * for one of written values, and either otherwise.
         */
        private Outcomes unsaid(Core.Read name) {
            return names.writtenOut(name) ? Outcomes.FIXED_UNNAMED : Outcomes.EITHER;
        }

        /** What {@code name} stands for and where, or null where it stands for no one value. */
        private Denotation valueOf(Core.Read name) {
            Denotation denoted = names.denotes(name);
            return Core.withoutStanding(denoted.value()) instanceof Core.Read same
                    && same.binding().equals(name.binding()) ? null : denoted;
        }
    }
}
