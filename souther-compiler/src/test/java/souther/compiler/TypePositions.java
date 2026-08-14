package souther.compiler;

import java.util.List;
import java.util.function.BinaryOperator;

/**
 * Every position the specification says a type is written in
 * (`a-type-is-written-in-a-type-position`), as whole sources to write one into.
 *
 * <p>One list, read by every sweep over the positions. Written out once per sweep it becomes a copy
 * of the specification's table that nothing compares against the other copies, and a position added
 * to the language is then covered by whichever sweeps happened to be updated. What each sweep asks
 * of a cell is its own; which cells there are is this.
 *
 * <p>{@code type} is the form written into the position, and {@code value} is something of that
 * form for the positions that need a value beside the type; a position that needs none ignores it.
 */
final class TypePositions {

    private TypePositions() {}

    /** A type position, as the whole source it is written in, given a form and a value of it. */
    record Position(String name, BinaryOperator<String> source) {

        /** The source with {@code type} written into this position. */
        String of(String type, String value) {
            return source.apply(type, value);
        }
    }

    private static final String CASES = """
            data A = { a: Int }
            data B = { b: Int }
            data Out = { v: Int }
            """;

    private static final String RUN = """

            behavior run : (i: Out) -> Out
                constructs Out

            let run (i) = Out { v = 1 }
            """;

    /** Two stages to write a composition over. The composition's inferred output is `A`. */
    private static final String STAGES = """

            behavior s1 : (i: Out) -> A
                constructs A

            let s1 (i) = A { a = 1 }

            behavior s2 : (i: A) -> A
                constructs A

            let s2 (i) = A { a = i.a }
            """;

    private static final String HEAD = "module demo\n\n" + CASES + "\n";

    /** A position whose source needs only the form written into it. */
    private static Position at(String name, String body) {
        return new Position(name, (type, value) -> HEAD + body.formatted(type) + RUN);
    }

    /** A position that has to be given a value of the form as well as the form. */
    private static Position valued(String name, String body) {
        return new Position(name, (type, value) -> HEAD + body.formatted(type, value) + RUN);
    }

    static final List<Position> ALL = List.of(
            at("data field", "data Hold = { x: %s }\n"),
            at("newtype base", "data Hold = %s\n"),
            at("behavior parameter",
                    "behavior go : (i: %s) -> A\n    constructs A\n\nlet go (i) = A { a = 1 }\n"),
            at("behavior output",
                    "behavior go : (i: Out) -> %s\n    constructs A\n\nlet go (i) = A { a = 1 }\n"),
            at("composition declared output", STAGES + "\nbehavior go = s1 >-> s2\n    -> %s\n"),
            new Position("composition output in exposing",
                    (type, value) ->
                            "module demo exposing (A, B, Out, s1, s2, run, go : %s)\n\n".formatted(type)
                                    + CASES + STAGES + "\nbehavior go = s1 >-> s2\n" + RUN),
            at("helper parameter", "let aux (h: %s) = 1\n"),
            valued("helper declared return", "let aux (n: Int) : %s = %s\n"),
            new Position("local binding annotation",
                    (type, value) -> HEAD + """

                            behavior run : (i: Out) -> Out
                                constructs Out, A

                            let run (i) = {
                                let a: %s = %s
                                Out { v = 1 }
                            }
                            """.formatted(type, value)),
            at("type argument", "let aux (h: List<%s>) = 1\n"),
            at("tuple member", "let aux (h: (%s, Int)) = 1\n"),
            at("function type parameter", "let aux (f: (%s) -> Int) = 1\n"),
            at("function type result", "let aux (f: (Int) -> %s) = 1\n"));
}
