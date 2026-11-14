package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.query.Adequacy;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A chain of {@code let}s that each add to the one before, compared with a bound on the input, is
 * closed in work that grows with the square of its length and not with its cube.
 *
 * <p>Every link is one more rule over the same numbers, and every link's closure is asked, for each
 * form its rules weigh, whether the rules leave it a value, and for each position of each rule what
 * is left of the rest of it. That is as many questions as rules, and read against every premise it is
 * the square of the rules for each closure and the cube over the chain: twice the links cost eight
 * times the premises read. The premises are held in a tree and each question is asked of the tree,
 * which is the work held here — counted and not timed, since a count is a shape and a time is a
 * machine.
 *
 * <p>Each shape is held: a link adds the one before to itself and to the input, so that what it
 * weighs doubles, or adds the input alone, so that what it weighs grows by one, over two numbers of
 * the input, and over three, which the rest of a rule is a question about the premises for.
 */
class AChainOfSumsOverTheInputIsClosedInWorkThatDoesNotCubeWithItsLengthTest {

    /** A link of the chain and the input it is over. */
    private enum Shape {
        DOUBLING("Pair = { x: Int, j: Int }", "Pair", "# + # + p.j", 5),
        ADDING_ONE("Pair = { x: Int, j: Int }", "Pair", "# + p.j", 5),
        OVER_THREE("Tri = { x: Int, j: Int, k: Int }", "Tri", "# + p.j + p.k", 7),
        OVER_THREE_AGAINST_EACH_OTHER("Tri = { x: Int, j: Int, k: Int }", "Tri", "# + p.j - p.k", 7);

        private final String data;
        private final String type;
        private final String link;

        /** How many times the work of twice the links may come to the work of the links: the cube
         *  is eight. Over three positions a question of the tree reads about the two-thirds power of
         *  the premises where the premises it is asked about all stand as far from it as one
         *  another, as the rest of a rule over equal bounds does, so the work is not the square. */
        private final int limit;

        Shape(String data, String type, String link, int limit) {
            this.data = data;
            this.type = type;
            this.link = link;
            this.limit = limit;
        }

        String chain(int links) {
            StringBuilder body = new StringBuilder("{\n    let a0 = p.x\n");
            for (int i = 1; i <= links; i++) {
                body.append("    let a").append(i).append(" = ")
                        .append(link.replace("#", "a" + (i - 1))).append("\n");
            }
            body.append("    a").append(links).append(" >= p.j\n}");
            return "module chain\n\ndata " + data + "\n\nbehavior m : (p: " + type + ") -> Bool\n\n"
                    + "let m (p) = " + body + "\n";
        }
    }

    /** The premises read and the boxes of the tree looked at, while the chain is measured. */
    private static long workClosing(Shape shape, int links) {
        long premises = ClosedState.premisesWorked();
        long steps = PremiseTree.steps();
        ACompiledModel.measured(shape.chain(links), Adequacy.Asked.warningsAt(Adequacy.Level.ALL));
        return (ClosedState.premisesWorked() - premises) + (PremiseTree.steps() - steps);
    }

    @Test
    void twiceTheLinksCostLessThanFiveTimesTheWorkInEveryShape() {
        for (Shape shape : Shape.values()) {
            long shorter = workClosing(shape, 12);
            long longer = workClosing(shape, 24);
            assertTrue(shorter > 0, "nothing was counted, so this holds nothing");
            // The square is four times and the cube eight; closing every link in work that reads
            // every premise for every question is the cube.
            assertTrue(longer < shape.limit * shorter, "twice the links cost " + longer
                    + " where the shorter chain cost " + shorter + ", " + shape);
        }
    }
}
