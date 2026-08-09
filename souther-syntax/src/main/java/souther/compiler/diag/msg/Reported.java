package souther.compiler.diag.msg;

/**
 * The role of being what a diagnostic is about — as opposed to what is said beside one.
 *
 * <p>Only these carry a {@link Code}, and only these can be a diagnostic's subject: {@code say}
 * takes a {@code Message & Reported} and a hint or a secondary label takes a
 * {@code Message & Supporting}. The two roles are disjoint, so being one is the same thing as being
 * usable as one — which is what the build's count of the rules something reports rests on. A hint
 * carrying a code would carry one nothing reads, and counted, a rule whose subjects had all moved to
 * another number would go on looking reported by the repair written under it.
 *
 * <p>Outside the {@link Message} hierarchy on purpose. A role admitted into it as a {@code
 * non-sealed} branch is a door out of the sealing: anything at all could implement the role and be a
 * message by doing so, past every rule the build holds the declared ones to. A role names what a
 * message is for, and a message is still only what {@code Message} permits.
 */
public interface Reported {
}
