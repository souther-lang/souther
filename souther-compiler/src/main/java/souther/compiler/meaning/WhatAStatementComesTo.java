package souther.compiler.meaning;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * What statements over the same parts come to, every way the parts can come out, held as the parts
 * come out one at a time in one order.
 *
 * <p>A statement is a node: the part asked first, and the statement left where it fails and where it
 * holds. Where both are the same statement the part turns nothing there, and the node is that
 * statement and asks no part. Each statement is held once, so two statements that come out the same
 * every way are one node, and whether a part turns a statement is whether the statement left with it
 * failing and the statement left with it holding are two nodes. That answer is the truth of the
 * statement and not of how it was written, which is what deciding whether to take cases apart on a
 * part asks: two ways of writing one statement are no part's doing.
 *
 * <p>A table of every way says the same, and holds twice as many ways for every part. Here only the
 * statements that are reached are held, and a part that turns nothing left is never asked.
 *
 * <p>The parts are numbers, asked lowest first.
 */
final class WhatAStatementComesTo {

    /** The statement that holds nowhere. */
    static final int NEVER = 0;

    /** The statement that holds wherever a row is. */
    static final int ALWAYS = 1;

    /** What an asking answers once its steps ran out, and what everything built on it answers. */
    static final int NOT_WORKED_OUT = -1;

    /** A part asked, with the statement left where it fails and where it holds. */
    private record Node(int part, int failing, int holding) {}

    private final List<Node> nodes = new ArrayList<>(List.of(
            new Node(Integer.MAX_VALUE, NEVER, NEVER), new Node(Integer.MAX_VALUE, ALWAYS, ALWAYS)));

    private final Map<Node, Integer> held = new HashMap<>();

    /** The part {@code statement} asks first, or {@link Integer#MAX_VALUE} where it asks none. */
    private int partAsked(int statement) {
        return nodes.get(statement).part();
    }

    /** {@code statement} with {@code part} come out {@code holds}, where {@code part} is the first
     *  it may ask. */
    private int left(int statement, int part, boolean holds) {
        Node node = nodes.get(statement);
        if (node.part() != part) {
            return statement;
        }
        return holds ? node.holding() : node.failing();
    }

    private int node(int part, int failing, int holding) {
        if (failing == holding) {
            return failing;
        }
        Node node = new Node(part, failing, holding);
        Integer at = held.get(node);
        if (at != null) {
            return at;
        }
        nodes.add(node);
        held.put(node, nodes.size() - 1);
        return nodes.size() - 1;
    }

    /** One asking: the statements it builds out of others, each step of it counted against a
     *  figure of its own, and what it built once remembered for it alone. */
    Asking asking(int steps) {
        return new Asking(steps);
    }

    /** How two statements are put together. */
    private enum Joined { BOTH, EITHER, ONE_NOT_THE_OTHER }

    private record Putting(Joined how, int one, int other) {}

    private record Leaving(int statement, int part, boolean holds) {}

    /**
     * Statements built out of others, every step counted.
     *
     * <p>A step is one statement built that this asking had not built before. Counted per asking,
     * and remembered per asking, so how far one gets is its own work and none of another's: a
     * statement some earlier asking built is still built again here, and counted.
     */
    final class Asking {

        private int left;

        private final Map<Putting, Integer> put = new HashMap<>();

        private final Map<Leaving, Integer> leftWith = new HashMap<>();

        private Asking(int steps) {
            this.left = steps;
        }

        /** {@code part} itself, held where {@code holds} and failing otherwise. */
        int part(int part, boolean holds) {
            return holds ? node(part, NEVER, ALWAYS) : node(part, ALWAYS, NEVER);
        }

        int both(int one, int other) {
            return joined(Joined.BOTH, one, other);
        }

        int either(int one, int other) {
            return joined(Joined.EITHER, one, other);
        }

        /** Where exactly one of the two holds. */
        int oneNotTheOther(int one, int other) {
            return joined(Joined.ONE_NOT_THE_OTHER, one, other);
        }

        int not(int statement) {
            return joined(Joined.ONE_NOT_THE_OTHER, statement, ALWAYS);
        }

        /** {@code statement} with {@code part} come out {@code holds}. */
        int with(int statement, int part, boolean holds) {
            if (statement < 0) {
                return NOT_WORKED_OUT;
            }
            int asked = partAsked(statement);
            if (asked > part) {
                return statement;
            }
            if (asked == part) {
                return left(statement, part, holds);
            }
            Leaving key = new Leaving(statement, part, holds);
            Integer known = leftWith.get(key);
            if (known != null) {
                return known;
            }
            if (!aStepIsLeft()) {
                return NOT_WORKED_OUT;
            }
            Node node = nodes.get(statement);
            int failing = with(node.failing(), part, holds);
            int holding = with(node.holding(), part, holds);
            int out = failing < 0 || holding < 0 ? NOT_WORKED_OUT
                    : node(asked, failing, holding);
            leftWith.put(key, out);
            return out;
        }

        /** Whether this asking ran out of steps somewhere. */
        boolean ranOut() {
            return left < 0;
        }

        private int joined(Joined how, int one, int other) {
            if (one < 0 || other < 0) {
                return NOT_WORKED_OUT;
            }
            Integer settled = settled(how, one, other);
            if (settled != null) {
                return settled;
            }
            Putting key = new Putting(how, Math.min(one, other), Math.max(one, other));
            Integer known = put.get(key);
            if (known != null) {
                return known;
            }
            if (!aStepIsLeft()) {
                return NOT_WORKED_OUT;
            }
            int part = Math.min(partAsked(one), partAsked(other));
            int failing = joined(how, left(one, part, false), left(other, part, false));
            int holding = joined(how, left(one, part, true), left(other, part, true));
            int out = failing < 0 || holding < 0 ? NOT_WORKED_OUT : node(part, failing, holding);
            put.put(key, out);
            return out;
        }

        /** What two statements come to put together where one of them says it alone, or null
         *  where neither does. */
        private static Integer settled(Joined how, int one, int other) {
            return switch (how) {
                case BOTH -> one == NEVER || other == NEVER ? Integer.valueOf(NEVER)
                        : one == ALWAYS ? Integer.valueOf(other)
                        : other == ALWAYS || one == other ? Integer.valueOf(one) : null;
                case EITHER -> one == ALWAYS || other == ALWAYS ? Integer.valueOf(ALWAYS)
                        : one == NEVER ? Integer.valueOf(other)
                        : other == NEVER || one == other ? Integer.valueOf(one) : null;
                case ONE_NOT_THE_OTHER -> one == other ? Integer.valueOf(NEVER)
                        : one == NEVER ? Integer.valueOf(other)
                        : other == NEVER ? Integer.valueOf(one)
                        : one == ALWAYS && other == ALWAYS ? Integer.valueOf(NEVER) : null;
            };
        }

        private boolean aStepIsLeft() {
            if (left <= 0) {
                left = -1;
                return false;
            }
            left--;
            return true;
        }
    }
}
