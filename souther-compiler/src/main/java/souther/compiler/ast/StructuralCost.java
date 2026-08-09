package souther.compiler.ast;

import java.util.ArrayList;
import java.util.List;

/**
 * What a source construct costs, and the bound a module is held to.
 *
 * <p>The compiler descends what it builds by recursion, so a construction that can make what it
 * builds deeper than what was read can take the stack with it. What bounds that is a number over
 * what the source wrote — the statements in a block, the arguments of an application, the values a
 * name reaches — and not the depth of any tree the compiler happens to build from it. The two are
 * not the same question: folding a block's statements into a spine or into a list changes the tree's
 * depth and changes nothing about the source, and a bound on the tree would make what compiles
 * depend on which one this compiler chose.
 *
 * <p>The cost composes:
 *
 * <pre>
 *   cost(a name, a literal)       = 1
 *   cost(a construct)             = 1 + the deepest of what it holds
 *   cost(an expanded application) = its argument count + the deepest of what it holds
 *   cost(a name reaching a value) = that value's cost, where the value is substituted
 * </pre>
 *
 * <p>An expanded application costs its arguments rather than one because each of them is bound:
 * expanding {@code h(a, b)} writes a binding per argument, and elaborating the expansion writes one
 * more per bound parameter. An application that is not expanded writes no bindings — a call to a
 * recursive helper is lowered to a method and called, and its arguments are arguments — so it costs
 * one, like any other construct. What is counted is what the compiler will build, and a call it
 * will not splice builds nothing per argument.
 *
 * <p>A block is counted in the steps its statements take, and a step is not always a binding: a
 * {@code guard} introduces no name and is one, because what follows it is written inside the case
 * it settles; an ordinary {@code let} is one; a {@code let} written with a pattern is as many as
 * the pattern binds. The rule for a construct counts a level each, and what a statement holds is
 * counted from where that statement stands rather than from the block's end — so a long block of
 * small statements and a short one holding something large can cost the same, which is the point:
 * what is counted is the longest way down, not two quantities added.
 *
 * <p>Neither number is read off the tree: both are counted from what the author wrote, and the tree
 * is only where they are read from.
 *
 * <p>The rules are checks and not a running total. The same body is asked about where it is
 * written, and again where a value carrying it is substituted into another — the second asks a
 * larger question than the first, and answering both does not charge the body twice.
 */
public final class StructuralCost {

    /**
     * The most any definition may cost.
     *
     * <p>Composed of the two bounds the language already states, because a bound on what may be
     * written has to leave the things that may be written room to be written together. The largest
     * application a definition may hold takes 255 arguments, which is what a generated method holds
     * ({@code [#generated-methods-fit-jvm-parameter-slots]}), and costs one more than that. Nesting
     * is bounded at 64 as the source is read ({@code [#source-nesting-is-bounded]}), and that
     * nesting is not refused afterwards for being nesting. Their sum is what it takes to write the
     * one inside the other, and a bound under it would be a bound at which two things the language
     * permits cannot be put together.
     *
     * <p>It is not derived from where the compiler's own walks give out. That number belongs to
     * this implementation and moves with it, and a bound read off it would make the language follow
     * the compiler. It runs the other way: this is what the compiler is required to hold, on the
     * stack it is supported on, and what the walks manage is how that requirement is checked rather
     * than where it came from.
     *
     * <p>Source needs far less. The deepest definition in the bundled prelude, the benchmark corpus
     * and souther-lang/examples costs 35, over 721 of them.
     */
    public static final int MAX = 320;

    private StructuralCost() {}

    /**
     * What {@code e} costs as written, with nothing substituted into it — so no application is an
     * expanded one, and none of them costs more than a construct.
     */
    public static int of(Ast.Expr e) {
        return of(e, _ -> UNKNOWN);
    }

    /** What {@link #of(Ast.Expr, Known)} is told where the cost of a subtree is not to be counted
     *  off the subtree. */
    public static final int UNKNOWN = -1;

    /**
     * What a subtree costs, where something already knows and this must not work it out again.
     *
     * <p>A block is the case there is. What it costs is the steps its statements take and what they
     * hold from where they stand, which is a fact about the statements the source wrote — and by the
     * time this could walk one, they are a spine of bindings, so walking it would be reading the
     * shape they were folded into. Whoever folded them says what they cost, and this takes that
     * answer rather than deriving one.
     */
    @FunctionalInterface
    public interface Known {
        int costOf(Ast.Expr e);
    }

    /** As {@link #of(Ast.Expr)}, taking {@code known}'s answer for any subtree it has one for. */
    public static int of(Ast.Expr e, Known known) {
        if (e == null) {
            return 0;
        }
        List<Ast.Expr> nodes = new ArrayList<>();
        List<Integer> above = new ArrayList<>();
        nodes.add(e);
        above.add(0);
        int most = 0;
        while (!nodes.isEmpty()) {
            Ast.Expr node = nodes.remove(nodes.size() - 1);
            int here = above.remove(above.size() - 1);
            if (node == null) {
                continue;
            }
            int said = known.costOf(node);
            if (said != UNKNOWN) {
                most = Math.max(most, here + said);
                continue;
            }
            int at = here + here(node, false);
            most = Math.max(most, at);
            Ast.forEachChild(node, child -> {
                nodes.add(child);
                above.add(at);
            });
        }
        return most;
    }

    /** What one node costs where it stands. A block's statements are a binding each by the time
     *  this reads them, so they are counted by the rule for a construct rather than by one of
     *  their own. */
    private static int here(Ast.Expr e, boolean expanded) {
        return expanded && e instanceof Ast.Apply apply ? Math.max(1, apply.args().size()) : 1;
    }

    /**
     * What a name reaches, for counting what substituting it would cost: the body substituted
     * there, or null where the name stands for itself.
     */
    @FunctionalInterface
    public interface Reaches {
        Ast.Expr substitutedAt(Ast.Var name);
    }

    /**
     * What {@code root} costs once everything it names is substituted into it, and the name the
     * count was inside when it passed {@link #MAX}.
     *
     * @param costs how much of the bound this takes, never more than one past it
     * @param past the name whose substitution took it past, or null where it did not go past
     */
    public record Composed(int costs, Ast.Var past) {

        /** Whether this is more than a definition may say. */
        public boolean isPastTheBound() {
            return past != null;
        }
    }

    /**
     * What {@code root} costs with what it names substituted into it, counted only as far as it has
     * to be.
     *
     * <p>Stopped one past the bound rather than finished. What is being asked is which side of the
     * bound this falls on, and a module whose values compose without end — a chain of ten thousand,
     * each naming the one before — is a question that can be answered after two hundred and
     * fifty-seven of them. Counting it out would walk the whole chain to say what the first stretch
     * of it already said.
     *
     * <p>A name already being substituted is not substituted again. Reaching the bound is not
     * enough to come back from a value defined as itself: {@code let v = v} is a body that is
     * nothing but the name, so going round it substitutes without ever counting a level, and the
     * count that was to stop the walk never moves. That module is refused as the cycle it is, but
     * not by this and not before it — this is asked before a body is expanded, which is earlier
     * than the expansion that finds the cycle by re-entering it.
     */
    public static Composed composed(Ast.Expr root, Reaches reaches) {
        List<Step> todo = new ArrayList<>();
        todo.add(new Step(root, 0, null, null));
        int most = 0;
        while (!todo.isEmpty()) {
            Step step = todo.remove(todo.size() - 1);
            Ast.Expr node = step.node();
            if (node == null) {
                continue;
            }
            if (node instanceof Ast.Var name) {
                Ast.Expr body = Path.holds(step.path(), name.reaches())
                        ? null
                        : reaches.substitutedAt(name);
                if (body != null) {
                    todo.add(new Step(body, step.above(), name,
                            new Path(name.reaches(), step.path())));
                    continue;
                }
            }
            int at = step.above() + here(node, isExpanded(node, reaches));
            most = Math.max(most, at);
            if (at > MAX) {
                return new Composed(at, step.by());
            }
            Ast.forEachChild(node, child ->
                    todo.add(new Step(child, at, step.by(), step.path())));
        }
        return new Composed(most, null);
    }

    /** Whether applying this splices a body here, which is what makes its arguments bindings. */
    private static boolean isExpanded(Ast.Expr e, Reaches reaches) {
        return e instanceof Ast.Apply apply
                && apply.function() instanceof Ast.Var applied
                && reaches.substitutedAt(applied) != null;
    }

    /** One node left to count: what is above it, the name whose substitution put it there, and the
     *  names being substituted around it. */
    private record Step(Ast.Expr node, int above, Ast.Var by, Path path) {}

    /**
     * What a step is inside the substitution of, innermost first. Shared between the steps that came
     * from one, which is what makes holding one per step cost nothing to copy.
     *
     * <p>Held by what each name reaches — the key the table is asked with — rather than by how it
     * was spelled. Two spellings can reach one declaration and one spelling can reach two, so a
     * path of spellings would call a walk round on itself where it is not, and let one through
     * where it is.
     */
    private record Path(String reaches, Path outer) {

        /** Whether {@code looked} is on {@code path} — of which nothing being substituted is one of
         *  the answers, and the one the root is asked with. */
        static boolean holds(Path path, String looked) {
            for (Path at = path; at != null; at = at.outer()) {
                if (at.reaches().equals(looked)) {
                    return true;
                }
            }
            return false;
        }
    }
}
