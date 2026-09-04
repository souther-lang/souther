package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Prepared;
import souther.test.Signatures;
import souther.test.TheBareRowNames;
import souther.test.WhatAModuleDeclares;

import java.lang.classfile.Signature;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Only a row is called a row.
 *
 * <p>A row is one line of an {@code example} or {@code fake} table. The things holding rows nest —
 * a block holds rows, a module's preparation holds blocks, a report holds a number of them — and
 * every one of those levels can be spelled {@code rows} without a reader being told which they have.
 * A count taken off the wrong level is a count of blocks that reads as a count of rows, and the
 * name is what produced the expectation.
 *
 * <p><b>Two prohibitions, because a level can be named twice.</b> A declaration names a level by
 * what it calls the member that answers it, and by what it calls the type that is it. Closing only
 * the member leaves a type free to be called {@code Rows} while holding blocks, which is where this
 * was found.
 *
 * <p><b>And one claim, because a prohibition alone cannot be held to.</b> Both prohibitions are
 * over what this module holds, so widening what counts as rows moves the population with them and
 * leaves nothing to report: a rule that admits more finds less. What the rule admits is said
 * separately, against shapes rather than against the module.
 *
 * <p><b>What is reserved is the bare name.</b> {@code row} and {@code rows} exactly, and the types
 * {@code Row} and {@code Rows} exactly. A compound name has a different head concept —
 * {@code rowCount} is a number, {@code RowReading} is a reading, {@code RowsRead} is what was read
 * — and a rule that took names apart into tokens would be a naming lint rather than this claim.
 * Nothing here says a compound name holds rows; only that the bare name is not available to
 * anything else.
 *
 * <p><b>What it is over is production declarations.</b> It reads the main class files of this
 * module, which is where the row vocabulary is declared and where a reader of this compiler meets
 * it. The modules beside it hold the same rule and say it themselves, each over its own classes.
 * Test fixtures, local variables and parameters are not part of the surface it protects: a
 * table-driven test's own {@code Row} is not a name any reader of the compiler resolves, and what a
 * method calls a value inside its body is not a declaration. Serialized vocabulary is outside it
 * too — a report's JSON key {@code "rows"} is a wire contract of its own and is not renamed by
 * anything said here.
 */
class OnlyARowIsCalledARowTest {

    /**
     * The rows of this compiler.
     *
     * <p>The declaration of what the word means. A value of one of these types is one row itself,
     * at whichever stage the type belongs to — what an author wrote, what the check settled, what a
     * run recorded, what a generator offered. A line stays a line all the way along, so the list is
     * a chain and not a layer.
     *
     * <p>What is not on it is everything that is <em>about</em> a row. An identity, a reference, an
     * id, a key, a reading, a verdict, a deadline and a unit of work each hold a row's whereabouts
     * beside something else, and a reader handed one of them under the bare name would take it for
     * the line.
     */
    private static final Set<String> ROWS = Set.of(
            "souther/compiler/ast/Ast$ExampleRow",
            "souther/compiler/ast/Ast$FakeRow",
            "souther/compiler/ast/Hir$ExampleRow",
            "souther/compiler/ast/Hir$FakeRow",
            "souther/compiler/examples/RecordedRow",
            "souther/compiler/observe/RowOutcome",
            "souther/compiler/partition/Generator$GeneratedRow",
            "souther/compiler/program/CheckedRow",
            "souther/compiler/query/OfferedRow",
            "souther/compiler/query/Output$RowsRead$ReadRow");

    /**
     * What a plurality of rows is held in.
     *
     * <p>What this compiler holds them in, and nothing else. A closed list is the point — a shape
     * nobody has decided about arrives as a failure rather than as a pass — so a shape nobody has
     * written yet is not admitted in advance either. A map from something to rows is the case that
     * made this worth closing: what its keys are is a second thing the value says, and a name that
     * does not say it leaves the reader to find out.
     */
    private static final Set<String> CONTAINERS = Set.of("java/util/List");

    /** A member called {@code row} or {@code rows} answers a row, or rows. */
    @Test
    void aMemberCalledRowAnswersARow() {
        assertEquals(List.of(),
                TheBareRowNames.takenIn(compiled(), each -> answersARow(each.type())),
                "a member called row or rows answers a row or rows, and these answer something else");
    }

    /** A type called {@code Row} or {@code Rows} is a row, or is rows. */
    @Test
    void aTypeCalledRowIsARow() {
        assertEquals(List.of(),
                TheBareRowNames.typesIn(compiled()).stream()
                        .filter(each -> !ROWS.contains(each)).toList(),
                "a type called Row or Rows is a row, and these are something else");
    }

    /**
     * And what the reserved name may answer is these shapes and no others.
     *
     * <p>The two prohibitions say what this module holds today, so an edit that widened what counts
     * as rows would go on passing — the population would move with it and nothing would be left to
     * report. So what the rule admits is claimed here against shapes: each is written out and run,
     * and widening the rule fails on the shape it newly admits.
     *
     * <p>The refusals are the ones that cost something. A plurality of pluralities is the shape
     * this whole rule came from: {@code rows().size()} over one is a count of groups read as a
     * count of rows.
     */
    @Test
    void andTheReservedNameAnswersTheseShapesAndNoOthers() {
        String row = "Lsouther/compiler/ast/Hir$ExampleRow;";
        Map<String, Boolean> shapes = new LinkedHashMap<>();
        shapes.put(row, true);                                  // a row
        shapes.put("Ljava/util/List<" + row + ">;", true);       // rows
        shapes.put("Ljava/util/List<+" + row + ">;", true);      // rows nothing writes to
        shapes.put("Ljava/util/List<Ljava/util/List<" + row + ">;>;", false);   // groups of rows
        shapes.put("[" + row, false);                           // a shape nobody has decided about
        shapes.put("[[" + row, false);                          // groups of them, as an array
        shapes.put("[Ljava/util/List<" + row + ">;", false);     // and the same, mixed
        shapes.put("Ljava/util/Map<Ljava/lang/String;Ljava/util/List<" + row + ">;>;",
                false);                                         // rows under a key
        shapes.put("Ljava/util/Set<" + row + ">;", false);       // another nobody has decided about
        shapes.put("Ljava/util/List<-" + row + ">;", false);     // rows go in, anything comes out
        shapes.put("Ljava/util/List<*>;", false);                // what it holds is unsaid
        shapes.put("Lsouther/compiler/check/Prepared$ForExamples;", false);   // what holds blocks
        shapes.put("I", false);                                 // a number of them

        Map<String, Boolean> answered = new LinkedHashMap<>();
        shapes.keySet().forEach(shape ->
                answered.put(shape, answersARow(Signature.parseFrom(shape))));
        assertEquals(shapes, answered, "what the reserved name may answer");
    }

    /**
     * And the prohibitions are over something.
     *
     * <p>Both pass on the empty set, which is also what a walk that read nothing answers. The rows
     * are the population the member rule is about — names it lets through rather than ones it never
     * met — and the classes are what the type rule ranges over.
     */
    @Test
    void andTheProhibitionsAreOverSomething() {
        List<String> internal = compiled().classes().stream()
                .map(each -> each.thisClass().asInternalName()).toList();
        // Named, rather than counted against a floor somebody chose: a walk that reached the
        // classes the rule is written about is what this is asking, and a number would be met by
        // any hundred of them.
        for (String each : ROWS) {
            assertTrue(internal.contains(each), () -> "the walk did not reach " + each);
        }
        assertFalse(compiled().taking(TheBareRowNames.MEMBERS).isEmpty(),
                "the reserved name is in use on what may hold it");
    }

    /**
     * Whether what a member answers is a row, or rows.
     *
     * <p>One row, or one container of rows, and no further. What holds rows does not recur: a list
     * of lists of rows is a plurality of pluralities, and its size is a count of groups. Answered
     * under the reserved name it would be read as a count of rows, which is the reading this whole
     * rule exists to remove — the one that came off {@code rows().rows().size()}.
     *
     * <p>A number is not rows: what it counts is not in it. Nor is an array of them — not because
     * an array could not hold rows, but because nothing here writes one, and admitting a shape in
     * advance is what {@link #CONTAINERS} is closed against.
     */
    private static boolean answersARow(Signature answered) {
        return answered instanceof Signature.ClassTypeSig cls
                && (isARow(cls)
                        || (CONTAINERS.contains(Signatures.named(cls))
                                && cls.typeArgs().size() == 1
                                && holdsARow(cls.typeArgs().getFirst())));
    }

    /** Whether a type is one of the rows themselves. */
    private static boolean isARow(Signature type) {
        return type instanceof Signature.ClassTypeSig cls && ROWS.contains(Signatures.named(cls));
    }

    /**
     * Whether a container's one type argument is a row.
     *
     * <p>What may be read out as a row. {@code ? extends} may — every element of it is one — and
     * {@code ? super} may not: what comes out of a list something writes rows into is whatever the
     * bound admits. A wildcard with no bound says nothing at all.
     */
    private static boolean holdsARow(Signature.TypeArg arg) {
        return arg instanceof Signature.TypeArg.Bounded bounded
                && bounded.wildcardIndicator()
                        != Signature.TypeArg.Bounded.WildcardIndicator.SUPER
                && isARow(bounded.boundType());
    }

    private static WhatAModuleDeclares compiled() {
        return WhatAModuleDeclares.of(Prepared.class);
    }
}
