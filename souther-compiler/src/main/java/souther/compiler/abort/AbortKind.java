package souther.compiler.abort;

/**
 * A way a Souther computation ends without a value, named by the reason the language gives for it
 * rather than by which site reaches it or which carrier reports it.
 *
 * <p>Backend-neutral. Nothing here says which JVM class is thrown, which Wasm code a host reads, or
 * which trap a native build raises — that mapping belongs to whichever output is emitting, exactly
 * as a {@link souther.compiler.core.Kernel}'s own machine form does. What this fixes is the smaller
 * fact every carrier's mapping has to answer for: the finite set of reasons the language itself
 * gives for a run ending with no value and no case.
 *
 * <p>A member here is one the specification states as its own abort, not one operation that happens
 * to reach it. {@code Int} overflow, a {@code Decimal} scale outside what the run time takes, a
 * temporal shift off the end of what it holds, and a {@code String.repeat} count no string could
 * hold are four different operations and one member — {@link #ANSWER_HAS_NO_PLACE} — because the
 * specification states one law for all four (`an-operation-refuses-only-what-its-own-answer-has-no-
 * place-for`) and each of the four cites it. Two operations are folded together only where the
 * specification itself gives them one reason; two are kept apart wherever it gives them two, even
 * where both are, say, a division — {@link #DIVISION_BY_ZERO} and {@link #ANSWER_HAS_NO_PLACE} are
 * both reached by the exact {@code /} operator, on a zero divisor and on an exponent past what
 * {@code Rational}'s own representation holds, and the specification is explicit that those are two
 * reasons and not one. {@code Int.truncatingDivide} answers a zero divisor as a case instead and
 * reaches only the second — see {@link #DIVISION_BY_ZERO}'s own note on that line.
 *
 * <p>A carrier's own reasons are not here. A bad arena mark, a document that is not JSON, a value
 * whose tag nothing knows — none of those is a Souther program ending without a value; they are an
 * ABI failing to carry one, and folding them in would make the language answer for a carrier's own
 * mistakes. Nor is a backend's own invariant failure — a fork a checker settled always answers,
 * reached anyway because a backend emitted the wrong test — a case of the language failing to give
 * a value, and it is not here either. Neither is the platform running out of room to finish a
 * computation the language itself owes an answer to: that is reported as the run failing, not as
 * the language's answer having a shape ({@code souther.runtime.OutOfRoom}).
 *
 * <p>Closed, on purpose and for the same reason {@link souther.compiler.core.Kernel} is: which ways
 * the language ends without a value is a decision of the language, not an extension point a backend
 * fills in. A reader switches over these and javac says which arms it has not answered — which is
 * what keeps a new member from landing in one backend's mapping while every other stays green and
 * wrong, the two hand-kept lists agreeing today only because one prose reading was done twice.
 */
public enum AbortKind {

    /**
     * A construction ran a {@code data}'s {@code invariant} clauses and the run did not keep one
     * (spec §invariant-abort). Reached only where nothing catches the failure first — an
     * {@code IfConstructed} that tests the same construction takes its else arm instead and never
     * reaches this.
     */
    INVARIANT_NOT_HELD,

    /**
     * A behavior's {@code ensures} relates what it is given to what it answers, and a run did not
     * keep it (spec §violation-destination). Where this is checked is a separate question, answered
     * by {@link souther.compiler.core.EnsuresEnforcement}: a behavior with no clause never reaches
     * this reason at all, and one this compilation has not decided the enforcement of is a question
     * {@link souther.compiler.core.EnsuresEnforcement#aborts} refuses rather than answers — "never
     * reaches this" and "this compilation does not say" are not the same claim, and only the first
     * is {@link AbortSet#NONE}.
     */
    ENSURES_NOT_HELD,

    /**
     * An {@code unreachable} the model wrote was reached: a premise the body declared cannot arise
     * did (spec §unreachable). A model bug for the same reason {@link #INVARIANT_NOT_HELD} is — a
     * declaration the model made and the run did not keep — and a different member because it is a
     * different declaration: a clause is about a value or a relation, {@code unreachable} is about
     * a position never being reached at all.
     */
    UNREACHABLE_REACHED,

    /**
     * An operation defined to abort on a zero divisor met one: {@code Int}'s {@code /} and
     * {@code floorMod}, {@code Decimal}'s {@code /}, {@code Rational}'s {@code /} (spec
     * §stdlib-int, §stdlib-decimal, §stdlib-rational). A named operation that answers
     * {@code DivisionByZero} as a case instead — {@code Int.truncatingDivide},
     * {@code Int.truncatingRemainder}, {@code Decimal.divide} — never reaches this: the
     * specification drew that line by name, and this reason exists only on the side of it that
     * did not become a case.
     */
    DIVISION_BY_ZERO,

    /**
     * The value an operation would answer with has no place in the type its answer is declared to
     * be — never because an intermediate a backend happened to compute through has none (spec
     * `an-operation-refuses-only-what-its-own-answer-has-no-place-for`, cited by §stdlib-int's
     * {@code Int} overflow, a {@code Decimal} scale outside what the run time takes, a temporal
     * shift off the end of what it holds, {@code String.repeat}'s and the padding operations'
     * count no string could hold, {@code List.rangeInclusive}'s span, and {@code Rational}'s own
     * narrowings to {@code Int} and to a scaled {@code Decimal}. One member for all of them because
     * the specification states one law and each of them cites it; a future operation that does not
     * cite that law is not this reason merely for resembling one that does.
     */
    ANSWER_HAS_NO_PLACE,

    /**
     * The bounds an operation was given do not name the thing they are asked to name, independent
     * of what any answer would be: {@code String.slice} with an index the string has not got, or a
     * {@code toExclusive} before {@code fromInclusive} (spec §stdlib-string). Kept apart
     * from {@link #ANSWER_HAS_NO_PLACE} because the two fail for different reasons even where both
     * sit on one operation's argument list — {@code slice}'s bounds may name nothing to slice at
     * all, where an {@code Int} overflow's operands are always positions a value exists at and it
     * is the answer that has none.
     */
    INVALID_BOUNDS,
}
