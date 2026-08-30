package souther.compiler.check;

/**
 * One written choice, told apart from every other by being this object.
 *
 * <p>Made once, where the {@code ||} is read, and copied wherever a conjunction distributes over
 * the choice — so however many places a branch of it turns up in the met-together reading, every
 * one of them answers for the same thing an author wrote. Identity and nothing else: two choices
 * spelled the same way are two decisions, which is the same reason the parts of a clause are filed
 * by the node and not by what a node is equal to.
 */
final class ChoiceId {
}
