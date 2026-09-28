package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BinOp;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * What an operator reads its operands as does not turn on which of them was written first.
 *
 * <p>Every rule that admits a pair of unlike types is asked of the pair, so what it settles is the
 * pair's too. A reading taken from one side's type answers differently for {@code x == y} and
 * {@code y == x}, and the difference reaches every reader that files a comparison by what it reads —
 * which is where two sums listing one set of cases were read in whichever of them came first. Each
 * pair below is written both ways round and the two readings are held to be one.
 */
class AnOperatorReadsItsOperandsAlikeWrittenEitherWayRoundTest {

    /** A pair of operands, written {@code a op b} and {@code b op a}. */
    private record Pair(String name, String params, String a, BinOp op, String spelled, String b,
                        String around) {

        String written(boolean turned) {
            String applied = turned ? b + " " + spelled + " " + a : a + " " + spelled + " " + b;
            return around.formatted(applied);
        }
    }

    private static final List<Pair> PAIRS = List.of(
            new Pair("sameCases", "x: Near, y: Far", "x", BinOp.EQ, "==", "y", "%s"),
            new Pair("sumAndCase", "s: Shape, c: Circle", "s", BinOp.EQ, "==", "c", "%s"),
            new Pair("unionAndCase", "n: Int, c: Circle", "shapeOf(n)", BinOp.EQ, "==", "c",
                    "%s"),
            new Pair("caseOfTwoSumsEqual", "x: X, s: First", "x", BinOp.EQ, "==", "s", "%s"),
            new Pair("caseOfTwoSumsOrdered", "x: X, s: First", "x", BinOp.LT, "<", "s", "%s"),
            new Pair("caseOrdered", "s: Stage", "s", BinOp.LT, "<", "Won", "%s"),
            new Pair("unionOrdered", "n: Int", "stageOf(n)", BinOp.LT, "<", "Prospecting", "%s"),
            new Pair("literalEqual", "a: Amount", "a", BinOp.EQ, "==", "100", "%s"),
            new Pair("literalOrdered", "a: Amount", "a", BinOp.LE, "<=", "100", "%s"),
            new Pair("exactEqual", "d: Decimal, j: Int", "d", BinOp.EQ, "==", "j / 2", "%s"),
            new Pair("exactOrdered", "i: Int, j: Int", "i", BinOp.LT, "<", "j / 2", "%s"),
            new Pair("exactSum", "i: Int, j: Int", "i", BinOp.ADD, "+", "j / 2", "%s > 1"),
            new Pair("bottomEqual", "xs: List<Int>, x: Int", "e", BinOp.EQ, "==", "x",
                    "List.any(e -> %s, List.fold((acc, y) -> acc, [], xs))"));

    private static final String MODULE = """
            module demo

            data Amount = Int

            data A
            data B
            data Near = A | B
            data Far  = A | B

            data X
            data Y
            data Z
            data First  = X | Y
            data Second = X | Z

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data Circle = { r: Int }
            data Square = { side: Int }
            data Shape  = Circle | Square

            let shapeOf (n: Int) : Circle | Square =
                if n > 0 then Circle { r = n } else Square { side = n }

            let stageOf (n: Int) : Won | Qualified = if n > 0 then Won else Qualified
            """;

    @Test
    void eachPairIsReadAlikeWrittenEitherWayRound() {
        List<String> differ = new ArrayList<>();
        for (Pair pair : PAIRS) {
            Core.Binary forward = applying(pair.name() + "Forward", pair.op());
            Core.Binary turned = applying(pair.name() + "Turned", pair.op());
            if (!forward.reading().equals(turned.reading())
                    || !forward.type().equals(turned.type())) {
                differ.add(pair.name() + ": " + forward.reading() + " " + forward.type() + " / "
                        + turned.reading() + " " + turned.type());
            }
        }
        assertEquals(List.of(), differ);
    }

    @Test
    void eachPairReachesTheRuleItIsNamedFor() {
        List<String> reached = new ArrayList<>();
        for (String name : List.of("sameCases", "caseOfTwoSumsEqual", "caseOfTwoSumsOrdered",
                "bottomEqual")) {
            Pair pair = PAIRS.stream().filter(each -> each.name().equals(name)).findFirst()
                    .orElseThrow();
            reached.add(name + " " + Type.show(assertInstanceOf(Core.BinaryReading.In.class,
                    applying(name + "Forward", pair.op()).reading()).type()));
        }
        assertEquals(List.of("sameCases A | B", "caseOfTwoSumsEqual X | Y",
                "caseOfTwoSumsOrdered First", "bottomEqual Int"), reached);
    }

    @Test
    void aSumAndTheUnionOfItsCasesAreReadAlike() {
        assertEquals(applying("sumAndCaseForward", BinOp.EQ).reading(),
                applying("unionAndCaseForward", BinOp.EQ).reading());
    }

    private static Core.Binary applying(String behavior, BinOp op) {
        Core body = bodies().behaviorBodies().get(behavior);
        assertNotNull(body, "`" + behavior + "` has a body");
        List<Core.Binary> found = new ArrayList<>();
        collect(body, op, found);
        assertEquals(1, found.size(), "`" + behavior + "` applies " + op + " once");
        return found.getFirst();
    }

    private static void collect(Core e, BinOp op, List<Core.Binary> out) {
        if (e instanceof Core.Binary b && b.op() == op) {
            out.add(b);
        }
        Core.forEachChild(e, child -> collect(child, op, out));
    }

    private static Bodies.Elaborated checked;

    private static Bodies.Elaborated bodies() {
        if (checked != null) {
            return checked;
        }
        StringBuilder source = new StringBuilder(MODULE);
        for (Pair pair : PAIRS) {
            for (boolean turned : List.of(false, true)) {
                String name = pair.name() + (turned ? "Turned" : "Forward");
                String names = String.join(", ", pair.params().split(": [^,]+(, )?"));
                source.append("\nbehavior ").append(name).append(" : (").append(pair.params())
                        .append(") -> Bool\n")
                        .append("let ").append(name).append(" (").append(names).append(") = ")
                        .append(pair.written(turned)).append('\n');
            }
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code() + " " + each.diagnostic().primary())
                        .toList(),
                "the model under test compiles");
        checked = compilation.db()
                .ask(new Bodies.Checked(compilation.modules().get(0))).value();
        assertNotNull(checked, "the model under test was checked");
        return checked;
    }
}
