package souther.compiler.examples;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;

/**
 * What stands in for a behavior's requirement while an example runs (spec §example-fakes).
 *
 * <p>Two things may: a {@code with} written on the row, and a {@code fake} table written beside it.
 * The row is looked at first, so a row that answers a dependency itself answers it whatever the
 * module says. A requirement neither of them answers is one nothing can run against, which is
 * E1908.
 *
 * <p>Said here rather than inside the verifier that reports it, because the question is asked twice
 * over: once by a run about to build a stand-in, and once by a reader that only wants to know what a
 * row still owes and has no values to build. What was written and where is handed back rather than a
 * yes or no, since those two do different things with it.
 *
 * <p>What a row contributes is the {@code with}s on it, taken as a list rather than as the row, so
 * that a row nobody has written yet can be asked the same question by contributing none.
 */
public final class ExampleProvisioning {

    private ExampleProvisioning() {}

    /** What was found to stand in, and where it was written. */
    public sealed interface Standin {

        /** The row answers this one itself, with a value that ignores what it is asked. */
        record OnTheRow(Hir.With written) implements Standin {}

        /** A table beside the rows answers it. */
        record InTheModule(Prepared.FakeTable table) implements Standin {}

        /** Nothing answers it, and a row whose target requires it cannot be run. */
        record Nothing() implements Standin {}
    }

    /**
     * What stands in for {@code dependency}, given what the row supplies of its own.
     *
     * @param onTheRow the {@code with}s written on the row; empty for a row not written yet
     */
    public static Standin standingIn(List<Hir.With> onTheRow, ValueName.Behavior dependency,
                                     Prepared.ForExamples module) {
        for (Hir.With written : onTheRow) {
            if (dependency.equals(written.standsInFor())) {
                return new Standin.OnTheRow(written);
            }
        }
        Prepared.FakeTable table = module.standingInFor(dependency);
        return table == null ? new Standin.Nothing() : new Standin.InTheModule(table);
    }

    /** Of {@code required}, the ones nothing stands in for, in the order they were required. */
    public static List<ValueName.Behavior> unsupplied(List<Hir.With> onTheRow,
                                                      List<ValueName.Behavior> required,
                                                      Prepared.ForExamples module) {
        List<ValueName.Behavior> owed = new ArrayList<>();
        for (ValueName.Behavior dependency : required) {
            if (standingIn(onTheRow, dependency, module) instanceof Standin.Nothing) {
                owed.add(dependency);
            }
        }
        return List.copyOf(owed);
    }
}
