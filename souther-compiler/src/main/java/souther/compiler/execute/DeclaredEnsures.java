package souther.compiler.execute;

import souther.compiler.core.Contract;
import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.ValueName;

import java.util.Map;

/**
 * What the behaviors a module's rows reach declare of what they answer, and where that module's own
 * compilation checks each of its own.
 *
 * <p>Two maps over two sets, and the difference is the point. {@code clauses} holds every reachable
 * behavior that states something, under the declaration it belongs to, because a value a row or a
 * stand-in gives for a behavior another module declares is held to that module's clause.
 * {@code placed} holds what {@code module} decided for each behavior it declares, and nothing for
 * another module's, which {@link EnsuresEnforcement#in} reads as not decided here rather than as a
 * table that was not filled. Joined into one map, the second distinction would be lost.
 *
 * <p>Together because what holds a stand-in needs both: the clause to run, and whether the code that
 * calls the stand-in already runs it.
 *
 * @param module  the module whose rows these are, and whose emitted code applies them
 * @param clauses what each reachable behavior declares, where it declares something
 * @param placed  where {@code module}'s compilation checks each behavior it declares
 */
public record DeclaredEnsures(String module, Map<ValueName.Behavior, Contract> clauses,
                              Map<ValueName.Behavior, EnsuresEnforcement> placed) {}
