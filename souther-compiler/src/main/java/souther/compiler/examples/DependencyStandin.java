package souther.compiler.examples;

import souther.compiler.types.ValueName;

import java.util.function.Function;

/**
 * What stands in for one dependency while a row runs: which dependency, how many inputs it takes, and
 * what it answers.
 *
 * <p>The whole stand-in for one dependency, which is not {@code ExampleStatements.Standin} — that is
 * one row of a fake's table, and a table has many. This is what the behavior is handed in place of the
 * dependency, however the row stated it: a {@code with dep = value} that ignores its inputs, or a
 * {@code fake dep | table} dispatched by its own rule.
 *
 * <p>What a stand-in <em>answers</em> is read where the row is evaluated, and is the same reading
 * whoever applies the behavior. Making it something a constructor can take is not: a unary dependency
 * becomes a {@code Behavior} proxy and any other arity a generated subclass of the dependency's base,
 * and both are classes of the loader the implementation being constructed comes from. So the answer is
 * here and the instance is the answerer's ({@link Answerer#applying}).
 *
 * <p>{@link #answers} takes and returns values of this compile's classes. That is not a general
 * protocol between a run and an answerer, and nothing needs it to be: a behavior with requirements is
 * one this compile generated a body for, and an injected behavior — the one an implementation can be
 * supplied for — has none, which {@code check.Requirements} answers for an injected name directly.
 * Which implementation and which stand-ins share an execution domain is {@link Answering}'s to
 * establish, and every domain that exists has them in one loader or has no stand-ins at all.
 *
 * <p>When an implementation supplied from outside a compile has to run a behavior that does have
 * requirements, this is what has to be designed again: the values going into and coming out of
 * {@link #answers} would then be crossing loaders, and the crossing that carries a row's arguments
 * ({@link Handed}) would have to carry a stand-in's arguments and its answer too.
 *
 * @param dependency the behavior this stands in for, as the declaration it is. The module is part of
 *                   it because the base an instance extends is generated where the behavior is
 *                   declared, which is not always the module the row is written in
 * @param inputs     how many inputs that behavior takes, which decides what an instance of it can be
 * @param answers    what it answers, for the arguments it is called with
 */
public record DependencyStandin(ValueName.Behavior dependency, int inputs,
                                Function<Object[], Object> answers) {}
