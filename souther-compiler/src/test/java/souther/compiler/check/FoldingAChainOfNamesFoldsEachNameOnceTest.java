package souther.compiler.check;

import souther.compiler.DefaultStdlib;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.ReadAs;
import souther.compiler.types.BinOp;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fold reads each name once, however many ways through the names lead to it.
 *
 * <p>{@code a(i) = a(i-1) + a(i-2)} reads the name two links back both straight and through the
 * one before it, so a fold that read a name again each way it was reached would cost what the
 * Fibonacci numbers count. Held as how the count grows with the chain rather than as how long it
 * takes: doubling the chain doubles what a fold reading each name once costs.
 *
 * <p>Asked of the names a reading was told of, which are read where the reading was told and not
 * where the name is — the place an environment made afresh each time a name is followed would have
 * every read of a name look like the first.
 */
class FoldingAChainOfNamesFoldsEachNameOnceTest {

    private static final SourcePos NOWHERE = new SourcePos(0, 0);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("m", "f");

    /** Short enough that a fold reading a name once per way to it still ends, a few million folds
     *  in, and is told apart by how far past three times the one before it the count runs. */
    private static final int[] LINKS = {8, 16, 32};

    @Test
    void doublingTheChainDoublesWhatFoldingItCosts() {
        SequencedMap<Integer, Long> folded = new LinkedHashMap<>();
        for (int links : LINKS) {
            folded.put(links, foldedOver(links));
        }
        Growth.eachAtMost(folded, 3, 1);
    }

    /** The same chain written as bindings in the tree, which a fold enters as it reads them. */
    @Test
    void aChainTheTreeBindsIsFoldedOnceAName() {
        SequencedMap<Integer, Long> folded = new LinkedHashMap<>();
        for (int links : LINKS) {
            folded.put(links, foldedInTheTree(links));
        }
        Growth.eachAtMost(folded, 3, 1);
    }

    /** The same chain as {@link #foldedOver}, bound by {@code let}s around a read of its last
     *  name — each value a binding of its own, {@code let t = a(i-1) + a(i-2) in t}, so a name read
     *  two ways enters the same binding from the same place twice. */
    private static long foldedInTheTree(int links) {
        Core.Binder[] binders = new Core.Binder[links];
        Core.Read[] reads = new Core.Read[links];
        Core[] values = new Core[links];
        for (int i = 0; i < links; i++) {
            BindingId id = new BindingId(OWNER, i);
            binders[i] = new Core.Binder("a" + i, id);
            reads[i] = new Core.Read("a" + i, id, Type.INT, NOWHERE);
            if (i < 2) {
                values[i] = new Core.Int(0, Type.INT, NOWHERE);
                continue;
            }
            BindingId inner = new BindingId(OWNER, links + i);
            values[i] = new Core.LetIn(new Core.Binder("t" + i, inner), Type.INT,
                    new Core.Binary(BinOp.ADD, reads[i - 1], reads[i - 2],
                            Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(),
                            Type.INT, NOWHERE),
                    new Core.Read("t" + i, inner, Type.INT, NOWHERE), Type.INT, NOWHERE);
        }
        Core body = reads[links - 1];
        for (int i = links - 1; i >= 0; i--) {
            body = new Core.LetIn(binders[i], Type.INT, values[i], body, Type.INT, NOWHERE);
        }
        long[] counting = {0};
        FoldedValue.FOLDED = counting;
        try {
            assertEquals(0L, CoreConstantEval.against(Symbols.none(DefaultStdlib.get()),
                    Denotations.none()).eval(body).orElseThrow(), "every name is nought");
        } finally {
            FoldedValue.FOLDED = null;
        }
        return counting[0];
    }

    /** And where an input is read, whose environment is its own: a guard over a text and a number
     *  the chain comes to, folded as the reading of the input folds them. */
    @Test
    void aChainAnInputIsReadUnderIsFoldedOnceAName() {
        SequencedMap<Integer, Long> folded = new LinkedHashMap<>();
        for (int links : LINKS) {
            folded.put(links, foldedWhereAnInputIsRead(links));
        }
        Growth.eachAtMost(folded, 3, 1);
    }

    private static long foldedWhereAnInputIsRead(int links) {
        StringBuilder lets = new StringBuilder("    let a0 = 0\n    let a1 = 0\n");
        for (int i = 2; i < links; i++) {
            lets.append("    let a").append(i).append(" = a").append(i - 1).append(" + a")
                    .append(i - 2).append('\n');
        }
        String model = """
                module demo
                data Bad
                behavior check : (x: Int, s: String) -> Int | Bad
                let check (x, s) = {
                %s    guard String.startsWith(String.repeat(a%d, "J"), s) else Bad
                    guard x >= a%d else Bad
                    0
                }
                """.formatted(lets, links - 1, links - 1);
        long[] counting = {0};
        FoldedValue.FOLDED = counting;
        try {
            Compilation compilation = Compilation.ofSource(model, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors().stream()
                    .map(e -> e.diagnostic().code()).toList(), "the model compiles");
        } finally {
            FoldedValue.FOLDED = null;
        }
        return counting[0];
    }

    /** The names folded while the last of {@code links} names is folded, each the sum of the two
     *  before it and the first two nought. */
    private static long foldedOver(int links) {
        Terms terms = RuleReadings.termsOfNoClauseFiled(Symbols.none(DefaultStdlib.get()),
                ReadAs.THE_COMPILATION_DOES);
        Denotations at = Denotations.none();
        Core.Read[] reads = new Core.Read[links];
        for (int i = 0; i < links; i++) {
            BindingId id = new BindingId(OWNER, i);
            Core value = i < 2 ? new Core.Int(0, Type.INT, NOWHERE)
                    : new Core.Binary(BinOp.ADD, reads[i - 1], reads[i - 2],
                            Core.BinaryReading.AS_THEY_STAND, ConstructOccurrence.unwritten(),
                            Type.INT, NOWHERE);
            at = at.binding(id, value, null, terms.placeSubject(id), null, null, null);
            reads[i] = new Core.Read("a" + i, id, Type.INT, NOWHERE);
        }
        long[] counting = {0};
        FoldedValue.FOLDED = counting;
        try {
            assertEquals(0L, CoreConstantEval.against(Symbols.none(DefaultStdlib.get()), at)
                    .eval(reads[links - 1]).orElseThrow(), "every name is nought");
        } finally {
            FoldedValue.FOLDED = null;
        }
        return counting[0];
    }
}
