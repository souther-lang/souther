package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.WhatWasCompiled;

import java.util.ArrayList;
import java.util.List;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Who follows what a name was given, written down with what stops them following it twice.
 *
 * <p>An environment answers with the value a name denotes, and what that value comes to is the
 * reader's own to work out (ADR-0111). So every reader of a binding has the same shape and the same
 * way of going wrong: a value may read two more names, each of those two more again, and a reader
 * that works the answer out afresh at each occurrence does the work as many times as the names
 * multiply out to, over a body that names one more of them. Three readers had it and each was found
 * by measuring that reader, which is finding a defect one instance at a time. This is the set.
 *
 * <p><b>Three ways of not following twice, and each row below uses one.</b> A reader that answers
 * with something keeps what it answered for the length of one walk, keyed by the binding. A reader
 * that fills a collection keeps the bindings it has followed, because everything a name holds is in
 * the collection after the first read of it. A reader that only steps from one name to the next,
 * without descending into what it finds, follows the chain once by walking it once, and a set that
 * stops it going round is all it needs.
 *
 * <p>Written down rather than read off the code, because which of the three a reader needs is not
 * something a walk over calls can tell — whether a reader descends is a fact about what it does
 * with the value. What this holds is that a reader added here is one somebody named, and not a
 * silence until the body that costs the exponent turns up.
 */
class WhoFollowsWhatANameWasGivenIsWrittenDownTest {

    /**
     * Every class that asks an environment what a name was given, and how each is bounded.
     *
     * <p>{@code CoreConstantEval} and {@code Terms} answer with something and hold it. {@code
     * Predicates} fills a map and holds the bindings it followed. {@code PathEngine} steps from
     * name to name without descending.
     */
    private static final List<String> FOLLOWERS = List.of(
            "souther.compiler.check.CoreConstantEval",
            "souther.compiler.check.PathEngine",
            "souther.compiler.check.Predicates",
            "souther.compiler.check.Terms");

    @Test
    void everyReaderThatFollowsANameIsWrittenDown() {
        assertEquals(FOLLOWERS,
                new ArrayList<>(new TreeSet<>(
                        WhatWasCompiled.callersOf(Denotations.class, "valueOf"))),
                "a reader added here follows a name to what it was given: say what stops it"
                        + " following one twice, and add the row");
    }
}
