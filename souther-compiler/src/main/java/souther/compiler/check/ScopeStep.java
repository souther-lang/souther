package souther.compiler.check;

import souther.compiler.core.Core;

import java.util.function.BiConsumer;

/**
 * What happens to the names in force on the way from a node into one of its children.
 *
 * <p>One question with one answer, and every walk that carries an environment asks it. A walk that
 * answered it for itself would answer it for the nodes it thought of and carry the environment
 * unchanged into every other one — and a name that one walk has entered and the next has not means
 * two things at one place in the body.
 *
 * <p>A step names the node that changes the scope and says nothing about what the change means.
 * What a {@code let} binds is {@link Terms#inside}'s answer and {@code InputReads}' answer, each in
 * its own vocabulary, and what choosing an arm binds is their answer to {@link Choice.Decides}. A
 * step carrying the binder and value taken apart would be a second place choosing what an
 * environment needs to know about a binding.
 *
 * <p>An arm of a plain {@code if} is a step as well, though it binds nothing: entering it is the
 * condition having gone one way, and whether that changes an environment is the environment's
 * question. A reader that wants to know what the step settles, rather than what it binds, is handed
 * the same {@link Choice.Decides} a reader of the choice is.
 */
public sealed interface ScopeStep {

    /** Nothing about the names changes: the child is read where its parent is. */
    record Same() implements ScopeStep {}

    /** Into the body of {@code binding}, where its name stands for what it was given. */
    record Let(Core.LetIn binding) implements ScopeStep {}

    /** Into the arm {@code decidedBy} decides. */
    record Chosen(Choice.Decides decidedBy) implements ScopeStep {}

    /** Into the body of {@code block}, which runs where something calls it and with its parameters
     *  given there. */
    record Block(Core.Block block) implements ScopeStep {}

    ScopeStep SAME = new Same();

    /**
     * Each child of {@code e} with the step into it, in {@link Core#forEachChild}'s order.
     *
     * <p>Exhaustive over {@code Core}, so a node kind added later stops the build here until somebody
     * says whether entering it changes what a name means. The nodes whose children are all read
     * where they stand are handed to {@link Core#forEachChild} rather than listed a second time;
     * which slots a node has is that method's answer, and for the nodes listed here the two are held
     * to the same children by a test.
     */
    static void forEachChild(Core e, BiConsumer<Core, ScopeStep> each) {
        switch (e) {
            case Core.If iff -> {
                each.accept(iff.cond(), SAME);
                each.accept(iff.then(), new Chosen(Choice.Decides.ofCondition(iff, true)));
                each.accept(iff.els(), new Chosen(Choice.Decides.ofCondition(iff, false)));
            }
            case Core.IfConstructed ic -> {
                each.accept(ic.construct(), SAME);
                each.accept(ic.then(), new Chosen(Choice.Decides.ofBuilt(ic)));
                for (Core.ElseArm arm : ic.els()) {
                    each.accept(arm.body(), new Chosen(Choice.Decides.ofDeparture(ic, arm)));
                }
            }
            case Core.LetIn li -> {
                each.accept(li.value(), SAME);
                each.accept(li.body(), new Let(li));
            }
            case Core.Block b -> each.accept(b.body(), new Block(b));
            case Core.Match m -> {
                each.accept(m.scrutinee(), SAME);
                for (Core.Case arm : m.cases()) {
                    each.accept(arm.body(), new Chosen(Choice.Decides.ofCase(m, arm)));
                }
            }
            case Core.Int _, Core.Decimal _, Core.Str _, Core.Bool _, Core.Temporal _, Core.Read _,
                 Core.UnitValue _, Core.MaterialisedValue _, Core.OptionNone _, Core.Unreachable _,
                 Core.Widen _, Core.Neg _, Core.FieldAccess _, Core.Binary _, Core.Call _,
                 Core.PreservedCall _, Core.Apply _, Core.ListLit _, Core.OptionSome _, Core.Tuple _,
                 Core.TupleGet _, Core.Construct _ ->
                    Core.forEachChild(e, child -> each.accept(child, SAME));
        }
    }
}
