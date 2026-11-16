package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.OptionalLong;

/**
 * How many elements the list a closure answers holds at most, whatever it is handed.
 *
 * <p>A bound that holds for every argument of the closure's parameter type, and so is asked of the
 * parameter's type alone: nothing a path to the closure's application says reaches it. A fact read
 * off the path that applies the closure would be a fact of that application, and a reader asking it
 * of another application would be handed it.
 *
 * <p>Asked of the engine a reading is made for, which is the one that knows what a type guarantees
 * of a value entered as a parameter. Everything else asks {@link #NONE}, which bounds nothing.
 */
interface AnswersForEveryArgument {

    /** Bounds nothing: every answer is unbounded. */
    AnswersForEveryArgument NONE = (answer, closure, at) -> OptionalLong.empty();

    /**
     * The most elements {@code answer}, the list {@code closure} answers, holds for every value of
     * the type of the closure's parameter, or empty where that is not shown.
     */
    OptionalLong mostOf(Core answer, Core.Block closure, Denotations at);
}
