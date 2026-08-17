package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.List;

/**
 * One behavior a construction requires injected, and the definitions that ask for it.
 *
 * <p>{@code dependency} is the behavior itself — the module that declares it and its name, because
 * two modules may declare a behavior of one name and a construction may want both. What it is
 * called in the generated class is not this: the class names its own fields, and this is what goes
 * in one. {@code requiredBy} names every
 * definition whose construction wants it: the behavior that declares it in {@code depends on}, or
 * the composition that names it as a stage. A dependency two stages of one composition share is one
 * requirement with two requesters — the composition holds one field for it and passes that field to
 * both (spec §composition-with-requirements), so answering with two requirements would inject it twice.
 *
 * <p>The requesters are what a diagnostic reads to say where a missing fake is wanted, without
 * walking the stages again to find out.
 */
public record BehaviorRequirement(ValueName.Behavior dependency, List<String> requiredBy) {}
