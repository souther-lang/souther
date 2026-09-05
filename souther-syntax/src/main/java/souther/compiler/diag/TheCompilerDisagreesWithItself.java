package souther.compiler.diag;

/**
 * A failure that says the compiler's own model contradicts itself, as opposed to one that says the
 * compiler could not follow a program.
 *
 * <p>What the two are is one name given two values, one clause given two answers, a region running
 * between two sources — as against a shape a walk has no rule for, where the run-time check stands
 * and a limit of an analysis may never reject a valid program.
 *
 * <p><b>No boundary asks about this.</b> One did, and asking was the mistake: a boundary that gives
 * up on everything except the kinds it recognises makes a limit of every failure nobody has named
 * yet, and nothing fails while it does. Where an analysis falls open now, what it falls open on is a
 * value something with the standing to say so made, and a failure with no such value behind it is
 * not a limit whatever its type
 * ({@code souther.compiler.check.WhatTheCheckCannotRead}).
 *
 * <p>So this names a family and is read by nobody. An interface and not a class, and here rather
 * than beside any one check, because the layers that raise one cannot share a superclass: a place
 * that is not a place is refused where regions become places, and the readings of a clause are
 * compared where clauses are read.
 */
public interface TheCompilerDisagreesWithItself {
}
