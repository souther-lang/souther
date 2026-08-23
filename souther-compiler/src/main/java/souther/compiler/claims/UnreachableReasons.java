package souther.compiler.claims;

import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;
import souther.compiler.coverage.NormalReturn;

import java.util.List;

/**
 * Why an expression answers nothing, in the words the model wrote.
 *
 * <p>Asked apart from {@link NormalReturn}, which answers whether and not why. An arm made of a
 * {@code match} whose arms each abort for a different reason has no one reason, and taking the first
 * would name whichever the author happened to write above the other. What comes back is every reason
 * on the paths that abort, so the caller can say the single one where there is one and say that there
 * are several where there are.
 *
 * <p>Every reason on those paths, and nothing after evaluation stops. A construction whose first
 * field aborts never evaluates the second, so a second {@code unreachable} written below it is not a
 * reason this value did not arrive — it is text that never runs. Paths that a fork keeps apart are
 * all read, because each of them is a way this expression fails to answer.
 *
 * <p>Which of them is first is the order the values are <em>evaluated</em> in, which is
 * {@link Evaluated}'s to say — for a construction that is the order the fields are declared rather
 * than the order the initializers are written, and asking it there is what keeps this reader and the
 * one that finds a body's first fork from disagreeing about what runs before what.
 */
public final class UnreachableReasons {

    /** One {@code unreachable} an expression reaches: what it says, and where it says it. */
    public record Said(String reason, souther.compiler.diag.SourcePos at) {}

    /**
     * Every {@code unreachable} reached along the paths that answer nothing, in the order they are
     * evaluated. Empty where the expression answers a value.
     *
     * <p>The words and the places come off one walk, since they are one reading: a reader wanting
     * the words and a reader wanting the place would otherwise walk the arm twice and could come to
     * disagree about which paths answer nothing. Repeats are kept, so that two arms aborting with
     * the same words still have two places between them; a caller wanting the reasons drops them.
     */
    public static List<Said> said(Core e, NormalReturn answering) {
        List<Said> found = new java.util.ArrayList<>();
        collect(e, answering, found);
        return List.copyOf(found);
    }

    private static void collect(Core e, NormalReturn answering, List<Said> into) {
        if (e == null || answering.at(e)) {
            return;
        }
        switch (e) {
            case Core.Unreachable u -> into.add(new Said(u.reason(), u.pos()));
            case Core.LetIn li -> collect(
                    answering.at(li.value()) ? li.body() : li.value(), answering, into);
            case Core.If iff -> {
                if (!answering.at(iff.cond())) {
                    collect(iff.cond(), answering, into);
                } else {
                    collect(iff.then(), answering, into);
                    collect(iff.els(), answering, into);
                }
            }
            case Core.Match m -> {
                if (!answering.at(m.scrutinee())) {
                    collect(m.scrutinee(), answering, into);
                } else {
                    m.cases().forEach(arm -> collect(arm.body(), answering, into));
                }
            }
            case Core.Construct nd -> {
                Core stops = evaluated(nd, answering);
                if (stops != null) {
                    collect(stops, answering, into);
                }
            }
            case Core.IfConstructed ic -> {
                Core stops = evaluated(ic.construct(), answering);
                if (stops != null) {
                    collect(stops, answering, into);
                } else {
                    collect(ic.then(), answering, into);
                    ic.els().forEach(arm -> collect(arm.body(), answering, into));
                }
            }
            // Anything else answers nothing because something it evaluates first does, and the rest
            // of what is written in it never runs.
            default -> {
                Core stops = firstThatAborts(Evaluated.inOrder(e), answering);
                if (stops != null) {
                    collect(stops, answering, into);
                }
            }
        }
    }

    /**
     * The value a construction stops at, or null where every one of them answers.
     *
     * <p>Read in the order the construction holds its fields, which is the order they are pushed:
     * the construction settled that when it was built, so what stops it is asked here rather than
     * worked out again from how the fields were written.
     */
    private static Core evaluated(Core.Construct nd, NormalReturn answering) {
        return firstThatAborts(Evaluated.inOrder(nd), answering);
    }

    /**
     * The first of what an expression evaluates that does not answer, which is where evaluation
     * stops and where every reason below it stops being one.
     *
     * <p>A step that runs only sometimes is read like any other here. This is reached only where the
     * whole expression answers nothing, and that reading already knows which operands a
     * short-circuiting operator runs ({@link souther.compiler.flow.ValueArrivals}) — so a right
     * operand that aborts is reached here exactly where every run really does reach it.
     */
    private static Core firstThatAborts(List<Evaluated.Step> evaluated, NormalReturn answering) {
        for (Evaluated.Step each : evaluated) {
            if (!answering.at(each.expression())) {
                return each.expression();
            }
        }
        return null;
    }


    private UnreachableReasons() {}
}
