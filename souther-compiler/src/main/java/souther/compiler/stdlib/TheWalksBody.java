package souther.compiler.stdlib;

import souther.compiler.ast.Hir;
import souther.compiler.core.TheWalk;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.ReachName;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * The library's walk read off its body ({@link TheWalk}), while the library is built.
 *
 * <p>The body is
 * <pre>
 *     match List.get(index, container) with
 *         | Some element -> walk(step, step(seed, element), container, index + 1)
 *         | None -> seed
 * </pre>
 * with its parameters in whatever order the declaration puts them and the step handed the seed and
 * the element in whatever order it is written. A body of any other shape is no walk, and a library
 * holding one is refused: every fold a program writes is a call of it, so a library whose walk this
 * cannot read is one nothing downstream could read a fold of.
 */
final class TheWalksBody {

    /** How many arguments the walk takes, and how many parameters its step does. */
    private static final int ARGUMENTS = 4;
    private static final int STEP_PARAMETERS = 2;

    private TheWalksBody() {}

    /**
     * The walk {@code declaration} is, as the declaration of {@code operation}, which reads an
     * element of its container with {@code get}.
     *
     * @throws IllegalStateException where the body is not the walk, naming what it is instead
     */
    static TheWalk readOff(ValueName.Stdlib.Operation operation, Hir.FnDef declaration,
                           ValueName.Stdlib.Operation get) {
        List<BindingId> params = new ArrayList<>();
        declaration.params().forEach(p -> params.add(p.binder().binding()));
        if (params.size() != ARGUMENTS) {
            throw notAWalk(operation, "it takes " + params.size() + " arguments");
        }
        if (!(declaration.body() instanceof Hir.FnBody.Written(Hir.Match match))) {
            throw notAWalk(operation, "its body is not a match");
        }
        if (!(match.scrutinee() instanceof Hir.Apply read) || !get.equals(libraryOperation(read))
                || read.args().size() != 2) {
            throw notAWalk(operation, "what it matches on is not " + get + " of two arguments");
        }
        int index = parameter(read.args().get(0), params);
        int container = parameter(read.args().get(1), params);
        if (index < 0 || container < 0 || index == container) {
            throw notAWalk(operation, "what it matches on is not " + get
                    + " of two of its own parameters");
        }
        Hir.Case some = armOf(match, TypeSymbol.SOME);
        Hir.Case none = armOf(match, TypeSymbol.NONE);
        if (some == null || none == null || match.cases().size() != 2 || some.binding() == null) {
            throw notAWalk(operation, "it does not answer exactly the two cases of an option");
        }
        int seed = parameter(none.body(), params);
        if (seed < 0 || seed == index || seed == container) {
            throw notAWalk(operation, "where nothing is at the index it does not answer a parameter"
                    + " of its own");
        }
        if (!(some.body() instanceof Hir.Apply again) || !operation.equals(libraryOperation(again))
                || again.args().size() != ARGUMENTS) {
            throw notAWalk(operation, "where something is at the index it does not call itself");
        }
        int step = -1;
        for (int at = 0; at < ARGUMENTS; at++) {
            if (at != seed && at != index && at != container) {
                step = at;
            }
        }
        if (parameter(again.args().get(step), params) != step
                || parameter(again.args().get(container), params) != container
                || !isTheNext(again.args().get(index), params.get(index))) {
            throw notAWalk(operation, "it does not walk on with its step and container to the next"
                    + " index");
        }
        if (!(again.args().get(seed) instanceof Hir.Apply applied)
                || parameter(applied.function(), params) != step
                || applied.args().size() != STEP_PARAMETERS) {
            throw notAWalk(operation, "it does not carry on with its step applied");
        }
        BindingId element = some.binding().binding();
        int accumulator = -1;
        int handed = -1;
        for (int at = 0; at < STEP_PARAMETERS; at++) {
            Hir.Expr arg = applied.args().get(at);
            if (parameter(arg, params) == seed) {
                accumulator = at;
            } else if (arg instanceof Hir.Var var && element.equals(local(var))) {
                handed = at;
            }
        }
        if (accumulator < 0 || handed < 0) {
            throw notAWalk(operation, "its step is not handed what it carries and the element");
        }
        return new TheWalk(operation, step, seed, container, index, accumulator, handed, get);
    }

    /** Which of {@code params} {@code e} reads, or -1 where it reads none of them. */
    private static int parameter(Hir.Expr e, List<BindingId> params) {
        return e instanceof Hir.Var var ? params.indexOf(local(var)) : -1;
    }

    /** The binding {@code var} reads, or null where it reads no local binding. */
    private static BindingId local(Hir.Var var) {
        return var.answered() != null
                && var.answered().reachedAs() instanceof ReachName.InScope(ValueName.Local local)
                ? local.id() : null;
    }

    /** The library operation {@code apply} applies, or null where it applies none. */
    private static ValueName.Stdlib.Operation libraryOperation(Hir.Apply apply) {
        return apply.function() instanceof Hir.Var var && var.answered() != null
                && var.answered().reachedAs() instanceof ReachName.OfLibrary(var operation)
                ? operation : null;
    }

    /** The arm of {@code match} taking the case {@code symbol} alone, or null where none does. */
    private static Hir.Case armOf(Hir.Match match, TypeSymbol symbol) {
        for (Hir.Case arm : match.cases()) {
            if (arm.caseTypes().size() == 1 && arm.caseTypes().get(0).answered() != null
                    && symbol.equals(arm.caseTypes().get(0).answered().type())) {
                return arm;
            }
        }
        return null;
    }

    /** Whether {@code e} is the index read at {@code index} with one added. */
    private static boolean isTheNext(Hir.Expr e, BindingId index) {
        if (!(e instanceof Hir.Binary(BinOp op, Hir.Expr left, Hir.Expr right, var _, var _, var _))
                || op != BinOp.ADD) {
            return false;
        }
        return (isIndex(left, index) && isOne(right)) || (isOne(left) && isIndex(right, index));
    }

    private static boolean isIndex(Hir.Expr e, BindingId index) {
        return e instanceof Hir.Var var && index.equals(local(var));
    }

    private static boolean isOne(Hir.Expr e) {
        return e instanceof Hir.IntLit(long value, var _, var _) && value == 1;
    }

    private static IllegalStateException notAWalk(ValueName.Stdlib.Operation operation,
                                                  String because) {
        return new IllegalStateException("the library publishes `" + operation + "` as its walk,"
                + " and its body is no walk: " + because);
    }
}
