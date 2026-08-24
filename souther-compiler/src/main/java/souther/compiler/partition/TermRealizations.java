package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.CountDomain;
import souther.compiler.numeric.Place;
import souther.compiler.semantics.TakenAs;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

/**
 * The values that put a term at a number, which is the other direction of {@link NumericTerm#read}.
 *
 * <p><b>Not its inverse.</b> Reading is not injective and building cannot undo it: many strings are
 * five long, and {@code Int.abs} answers three at three and at minus three. What holds is one way
 * round — every value built here reads back as the number it was built for. Written as an inverse,
 * the second operation to be added would have been the one that broke it, and the way it would have
 * broken is a row offered at an edge it does not stand on.
 *
 * <p>And whether anything exists to build is a third statement, declared of the operation
 * ({@code EveryAnswerItCanGiveHasASourceValue}) and asked where an edge is claimed to be writable.
 * A reader that took "there is an arm for this" for "this always builds" would promise a row for
 * every count of a {@code Set<Bool>}.
 *
 * <p>Here and not on the term. What a term is measured by and what it reads are answers about the
 * quantity; what a value of it looks like written down is the generator's, and a term that answered
 * it would name the generator's own vocabulary from {@code inputs} — a dependency the wrong way
 * round. What the term owes is the identity, which is the operation, and the arms below are keyed on
 * what {@code semantics} declares of it.
 */
final class TermRealizations {

    /** What building values that answer a number came to. */
    sealed interface Realization {

        /**
         * Values that answer it, and what was not built.
         *
         * <p>Two halves of one answer, as {@link Witnesses.Sized} keeps them. A caller reading only
         * the first says every value was refused where some were never built, which is a different
         * thing to tell an author.
         */
        record Built(List<FixtureTemplate> values,
                     Generator.UnresolvedCombination.Reason heldBack) implements Realization {

            public Built {
                values = List.copyOf(values);
                if (values.isEmpty()) {
                    throw new IllegalArgumentException(
                            "a realization that built nothing is one that built none, and says why");
                }
            }
        }

        /** Nothing here writes a value answering it, and this is what stopped there being one. */
        record BuiltNone(Generator.UnresolvedCombination.Reason why) implements Realization {}
    }

    /**
     * The values that stand at {@code answer} for {@code term}, given what the position holds.
     *
     * <p>Two arms and no default, the way {@link NumericTerm#read} has two. Which of them a term
     * takes is what the term <em>is</em> — the position's own content, or what an operation answered
     * of it — and that is the one question about a term the variant genuinely settles: the content
     * of a location is the number written at it, and a number an operation answered is met by
     * whatever answers it.
     */
    static Realization at(NumericTerm term, Type sourceType, Carrier answered, Place answer,
                          Symbols symbols, ReadingPolicy policy) {
        if (sourceType == null) {
            return new Realization.BuiltNone(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        return switch (term) {
            // Written by the carrier the line was drawn on, and wearing every name the position
            // declares. Read off the boundary's own shape instead, a count on one carrier could be
            // written as a literal of another — which is how a date-time's second count reached a
            // row as an `Int`, and the decoder refused it with the report saying only that every
            // value tried had been refused.
            case NumericTerm.ValueOf _ ->
                    oneValue(FixtureTemplate.on(answered, answer, symbols.scope()::reach),
                            sourceType, symbols);
            case NumericTerm.TakenOf taken ->
                    taken(taken.takenAs(), sourceType, answered, answer, symbols, policy);
        };
    }

    /**
     * The values a given operation answers a number at.
     *
     * <p>One arm per declared account of what such an operation takes, and no default — the same
     * closure the reading is under, so an account added to {@code semantics} cannot be read off a
     * row without also being writable onto one. Split between two switches that did not have to
     * agree, an operation would have gained a boundary nobody could write a row for, and the report
     * would have said only that every value tried was refused.
     */
    private static Realization taken(TakenAs how, Type sourceType, Carrier answered, Place answer,
                                     Symbols symbols, ReadingPolicy policy) {
        return switch (how) {
            case TakenAs.HowManyItHolds _ -> holding(sourceType, answer, symbols, policy);
            case TakenAs.AbsoluteMagnitude _ ->
                    eitherSideOfNought(sourceType, answered, answer, symbols);
        };
    }

    /** Values of the position holding exactly that many, which is {@link Witnesses}' answer. */
    private static Realization holding(Type sourceType, Place answer, Symbols symbols,
                                       ReadingPolicy policy) {
        int many = CountDomain.asCount(answer);
        if (many < 0) {
            return new Realization.BuiltNone(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        Type holder = TypeOps.base(sourceType, symbols);
        Witnesses.Sized built = Witnesses.ofSize(holder, many, symbols, policy, Set.of());
        if (built.values().isEmpty()) {
            return new Realization.BuiltNone(
                    Witnesses.reasonForSize(holder, many, policy, symbols));
        }
        List<FixtureTemplate> out = new ArrayList<>();
        for (FixtureTemplate each : built.values()) {
            out.add(Witnesses.wrapped(sourceType, each, symbols));
        }
        return new Realization.Built(out, built.heldBack());
    }

    /**
     * The two numbers a magnitude is answered at, which is the number and its negation.
     *
     * <p>Both, and the positive one first. They are one edge and not two — a row at either stands at
     * the same boundary — so offering only one would call an edge unwritable wherever the position's
     * rules happen to exclude that side. At nought the two are the same value and one is offered.
     *
     * <p>On the order the value is written on, which for these operations is the order the answer is
     * measured on as well. Written on the answer's order without asking, an operation reading a date
     * and answering a count would put a whole number where a date goes.
     */
    private static Realization eitherSideOfNought(Type sourceType, Carrier answered, Place answer,
                                                  Symbols symbols) {
        if (!(answer instanceof Count count)) {
            return new Realization.BuiltNone(
                    Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE);
        }
        List<Place> both = count.signum() == 0 ? List.of(count) : List.of(count, count.negate());
        List<FixtureTemplate> out = new ArrayList<>();
        for (Place each : both) {
            FixtureTemplate standing = Witnesses.wrapped(sourceType,
                    FixtureTemplate.on(answered, each, symbols.scope()::reach), symbols);
            if (standing != null) {
                out.add(standing);
            }
        }
        return out.isEmpty()
                ? new Realization.BuiltNone(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : new Realization.Built(out, null);
    }

    /** One value, wearing every name the position declares, or the reason there is none. */
    private static Realization oneValue(FixtureTemplate bare, Type sourceType, Symbols symbols) {
        FixtureTemplate standing = Witnesses.wrapped(sourceType, bare, symbols);
        return standing == null
                ? new Realization.BuiltNone(
                        Generator.UnresolvedCombination.Reason.NOTHING_COMPOSES_ONE)
                : new Realization.Built(List.of(standing), null);
    }

    private TermRealizations() {}
}
