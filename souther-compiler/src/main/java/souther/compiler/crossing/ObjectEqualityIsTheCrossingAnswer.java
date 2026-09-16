package souther.compiler.crossing;

/**
 * A value a collection may hold where two builds' declarations are compared.
 *
 * <p>A set compares what it holds, and a map compares its keys, by the equality the platform asks
 * of any object. Where a value of this kind is held in one, that equality has settled a question
 * the comparison of two builds was written to settle — and it is right to let it exactly while the
 * two answer the same thing about the value. That is a claim about the value, and it is made here.
 *
 * <p><b>Not the claim beside it.</b> {@link DelegatedEqualityIsTheCrossingAnswer} is about the
 * comparison a form gets when the walk holding two declarations together has nothing of its own to
 * say about it, and what that hands the two sides to is the language's answer about written values:
 * a decimal written two ways is one value there and two objects here. So the two are separate
 * claims about separate equalities, neither implies the other, and a value that is both says both.
 *
 * <p><b>What a collection asks is more than equality.</b> A hashed set finds what it holds by the
 * number the value answers first and compares only what that number gathered, so what is claimed
 * here rests on the value keeping the agreement between the two that any object owes. A value
 * answering a number of its own that reads less than its equality does is one a set loses, and that
 * is not a thing this says is all right.
 *
 * <p>A value whose claim rests on a representation it can name says the stronger thing instead
 * ({@link ObjectEqualityIsRepresentedByWhatItStandsFor}).
 */
public interface ObjectEqualityIsTheCrossingAnswer {
}
