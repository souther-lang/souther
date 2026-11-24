package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comment stays on the member it was written about, whichever way the grammar writes that member.
 *
 * <p>The cases here are the ways a member can be written rather than the constructs that have
 * members: a member is a node, or a bare identifier the enclosing construct holds directly, or a
 * segment of a chain, or absent because the construct is empty, or a part of an expression with no
 * line of its own. A sum's cases needed their own answer because they are identifiers, and the
 * answer was written for sums alone — which left an import's names and a {@code constructs} clause's
 * names, the same way of writing a member under a different construct, still losing theirs.
 *
 * <p>The survival sweep cannot ask this. A comment moved from one member to the next is one comment
 * in and one comment out, and the code around it is unchanged; what changed is the only thing a
 * comment is for.
 *
 * <p>So what is asked is the comment's neighbour. A comment on a line of its own is about what
 * follows it and one at the end of a line is about what it follows, so the code token it is next to
 * is the member it is about, and the formatter is free to lay everything else out as it likes: the
 * comment is next to the same token after as before. The layout is the other tests' to hold.
 */
class ACommentKeepsItsMemberHoweverItIsWrittenTest {

    /** Each way of writing a member, the source that writes a comment about one of them. */
    private static final Map<String, String> WRITTEN = new LinkedHashMap<>();

    static {
        WRITTEN.put("a node: a field of a product block", """
                module m
                data D =
                    { a: Int
                    // about b
                    , b: Int
                    }
                """);
        WRITTEN.put("an identifier the construct holds directly: the names an import lists", """
                module m
                import other.mod (
                    A,
                    // about B
                    B
                )
                data O = { n: Int }
                """);
        WRITTEN.put("an identifier of a clause, which is not a list of names", """
                module m
                data A = { n: Int }
                data B = { n: Int }
                behavior f : (n: Int) -> A | B
                    constructs A,
                    // about B
                    B
                let f (n) = A { n = n }
                """);
        // The clauses are the construct's next lines, so a comment ending the header's line is not
        // a comment about them.
        WRITTEN.put("the tail of a header line: a behavior's return type, with clauses under it", """
                module m
                data A = { n: Int }
                behavior f : (n: Int) -> A   // result
                    constructs A
                let f (n) = A { n = n }
                """);
        WRITTEN.put("the tail of a data header: what a newtype wraps, with an invariant under it", """
                module m
                data Positive = Int   // representation
                    invariant value > 0
                """);
        WRITTEN.put("a segment of a pipeline", """
                module m
                data O = { n: Int }
                let g (x: Int) = x
                let h (x: Int) = x
                behavior f : (n: Int) -> O constructs O
                let f (n) = O { n = n
                    |> g
                    // about h
                    |> h }
                """);
        // The parameter list goes down the page with it: a comment cannot share the line after it,
        // so every group holding one is written broken. What the comment is about is unchanged.
        WRITTEN.put("a member of a written union", """
                module m
                data A = { n: Int }
                data B = { n: Int }
                behavior f : (n: Int) -> A
                    // exceptional result
                    | B
                let f (n) = A { n = n }
                """);
        // The parser reads `1 |> b |> c` as nesting and the layout writes one run of segments, so
        // what the comment is about, the inner `1 |> b`, is not a construct the output has a line
        // for. Its segment is.
        WRITTEN.put("part of a run the layout flattens", """
                module m
                let b (x: Int) = x
                let c (x: Int) = x
                let value = 1
                    |> b   // about the b stage
                    |> c
                """);
        WRITTEN.put("a segment of an operator run, at the end of its line", """
                module m
                let value = 1
                    + 2   // about the second term
                    + 3
                """);
        WRITTEN.put("a segment of an operator run, above it", """
                module m
                let value = 1
                    // about the second term
                    + 2
                    + 3
                """);
        WRITTEN.put("a member of a nested bracketed construct: a type argument", """
                module m
                data D =
                    { xs: List<
                        // element type
                        Int
                      >
                    }
                """);
        // What closes a type's arguments is the same angle bracket the grammar compares with.
        WRITTEN.put("under the last member of a nested bracketed construct", """
                module m
                data D =
                    { xs: List<
                        Int
                        // why Int is allowed
                      >
                    }
                """);
        // A construct written over several lines has more lines than its last, and `data D =`
        // ends one of them.
        WRITTEN.put("the line a construct opens with", """
                module m
                data D =   // about the block
                    { a: Int
                    , b: Int
                    }
                """);
        WRITTEN.put("a row's input, a segment of the chain a row is written as", """
                module m
                let helper (n: Int) = n

                example helper
                    | (2)   // input
                        -> 2
                """);
        WRITTEN.put("the head of a chain: an example row's description", """
                module m
                let helper (n: Int) = n

                example helper
                    | "doubles"   // scenario description
                        : (2) -> 2
                """);
        // A comment written after code on the same line was written about that code. It used to be
        // handed to whatever was declared next, which is a different claim about the same words.
        WRITTEN.put("the declaration it was written after", """
                module m
                data WebForm
                data PhoneInquiry
                data Inbound = WebForm | PhoneInquiry      // three units; nothing to attribute
                data LeadSource = Inbound
                """);
        // The same words in the same place in the child list, told apart by the whitespace in
        // front of them: the one below carries the newline that ended the line above it and the one
        // beside does not. Both are here because either alone is satisfied by a formatter that
        // treats every comment the same way.
        WRITTEN.put("a field, the comment beside it", """
                module m
                data D =
                    { a: Int   // the comment
                    , b: Int
                    }
                """);
        WRITTEN.put("a field, the comment below it", """
                module m
                data D =
                    { a: Int
                    // the comment
                    , b: Int
                    }
                """);
        WRITTEN.put("a field whose type ends in an optional mark", """
                module m
                data AccountId = String
                data DomainName = String
                data Industry
                data Account =
                    { id: AccountId
                    , domain: DomainName?         // an honest optional
                    , industry: Industry
                    }
                """);
        // A sum's cases are identifiers rather than nodes, so a case cannot be named the way a
        // field can. The comment is held against where the identifier is instead.
        WRITTEN.put("a sum case", """
                module m
                data A
                data B
                data C
                data S = A   // about A
                    | B
                    | C
                """);
        // In a list whose members are separated rather than opened the comment goes after the
        // comma: the comma is on that line too, and one written after the comment would be inside
        // it.
        WRITTEN.put("a member followed by a comma", """
                module m
                data O = { a: Int, b: Int }
                behavior f : (n: Int) -> O constructs O
                let f (n) = O {
                  a = n,   // the first
                  b = n
                }
                """);
        WRITTEN.put("a match arm", """
                module m
                data A
                data B
                data S = A | B
                data O = { n: Int }
                behavior f : (s: S) -> O constructs O
                let f (s) = O { n = match s with
                  | A -> 1   // the first
                  | B -> 2 }
                """);
        // Both are written one to a line, and neither was asked for its comments.
        WRITTEN.put("an attempt's departure, above it", """
                module m
                data Amount = Int
                    invariant value > 0
                data O = { n: Int }
                behavior f : (n: Int) -> O | Amount constructs O, Amount
                let f (n) = {
                    guard Amount(n) as a else
                        // why this arm
                        | value -> Amount(1)
                    O { n = a.value }
                }
                """);
        WRITTEN.put("a pipeline's stage, above it", """
                module m exposing ( p )
                data A = { n: Int }
                data B = { n: Int }
                behavior one : (a: A) -> B constructs B
                behavior p =
                    one
                    // why this stage
                    >-> one
                """);
    }

    private static final Pattern TOKEN = Pattern.compile("[A-Za-z0-9_]+|\\S");

    /**
     * What each comment of {@code text} is next to, in the order they are written: the first code
     * token after one on a line of its own, and the last code token before one at the end of a line.
     */
    private static List<String> neighbours(String text) {
        String[] lines = text.split("\n", -1);
        List<String> out = new ArrayList<>();
        for (int at = 0; at < lines.length; at++) {
            int slashes = lines[at].indexOf("//");
            if (slashes < 0) {
                continue;
            }
            String comment = lines[at].substring(slashes).strip();
            String code = lines[at].substring(0, slashes);
            if (code.isBlank()) {
                int next = at + 1;
                while (next < lines.length && (lines[next].isBlank()
                        || lines[next].strip().startsWith("//"))) {
                    next++;
                }
                Matcher first = TOKEN.matcher(lines[next]);
                first.find();
                out.add(comment + " is above " + first.group());
            } else {
                Matcher tokens = TOKEN.matcher(code);
                String last = null;
                while (tokens.find()) {
                    last = tokens.group();
                }
                out.add(comment + " is after " + last);
            }
        }
        return out;
    }

    /** Each comment is next to the code token it was next to, whichever way its member is written. */
    @Test
    void aCommentIsNextToTheSameCodeWhicheverWayItsMemberIsWritten() {
        for (Map.Entry<String, String> each : WRITTEN.entrySet()) {
            List<String> before = neighbours(each.getValue());
            assertFalse(before.isEmpty(), each.getKey() + ": the source has a comment");
            assertEquals(before, neighbours(Formatter.format(each.getValue())), each.getKey());
        }
    }

    /**
     * One member written as several identifiers. A comment anywhere in the name is about the
     * whole name, so the two ends of the run have to agree on which member they are — reading each
     * identifier as a member of its own left the comment owned by something nobody asked for. The
     * comment goes above the clause that holds the name, which is further than it was written.
     */
    @Test
    void aMemberWrittenAsSeveralIdentifiers() {
        assertEquals("""
                module m

                data A =
                    { n: Int
                    }
                behavior f : (n: Int) -> A
                    // why this one
                    constructs other.A
                let f (n) = A { n = n }
                """, Formatter.format("""
                module m
                data A = { n: Int }
                behavior f : (n: Int) -> A
                    constructs other.
                        // why this one
                        A
                let f (n) = A { n = n }
                """));
    }

    /**
     * Written about one part of a row, which the layout writes as a chain of segments the way it
     * writes a pipeline. A row's input and its expected value are segments, and so is a match arm's
     * body; none of the three was asked what was written about it, so all three answered with the
     * row or the arm. The connector moves to the other side of the comment, so the comment is next
     * to the connector and not to what it was written above.
     */
    @Test
    void aPartOfARowWrittenAsAChain() {
        assertEquals("""
                module m

                let helper (n: Int) = n

                example helper
                    | (2)
                        // expected result
                        -> 2
                """, Formatter.format("""
                module m
                let helper (n: Int) = n

                example helper
                    | (2) ->
                        // expected result
                        2
                """));
    }

    /** A match arm's body is a segment of the same shape, and was the third instance of the same
     * miss. */
    @Test
    void andAMatchArmsBody() {
        assertEquals("""
                module m

                data A
                data B
                data S = A | B
                data O =
                    { n: Int
                    }
                behavior f : (s: S) -> O
                    constructs O
                let f (s) =
                    O {
                        n = match s with
                            | A
                                // result for A
                                -> 1
                            | B -> 2
                    }
                """, Formatter.format("""
                module m
                data A
                data B
                data S = A | B
                data O = { n: Int }
                behavior f : (s: S) -> O constructs O
                let f (s) = O { n = match s with
                    | A ->
                        // result for A
                        1
                    | B -> 2 }
                """));
    }

    /** No member to be about: the comment was written above the construct, and stays above it rather
     * than moving inside where the construct's own end comments go. */
    @Test
    void aConstructWithNoMemberToBeAbout() {
        assertEquals("""
                module m

                data O =
                    { xs: List<Int>
                    }
                behavior f : () -> O
                    constructs O
                let f =
                    O {
                        // empty for now
                        xs = []
                    }
                """, Formatter.format("""
                module m
                data O = { xs: List<Int> }
                behavior f : () -> O constructs O
                let f = O { xs =
                    // empty for now
                    [] }
                """));
    }

    /** Written as part of an expression, which has no line of its own. The comment goes to the end
     * of the line the construct holding it ends, which is further than it was written and is what
     * keeps it out of the middle of a line. */
    @Test
    void aPartOfAnExpressionWithNoLineOfItsOwn() {
        assertEquals("""
                module m

                data One
                data Two
                let value (n: Int) = if n > 0 then One else Two // about the test
                """, Formatter.format("""
                module m
                data One
                data Two
                let value (n: Int) = if n > 0   // about the test
                    then One else Two
                """));
    }
}
