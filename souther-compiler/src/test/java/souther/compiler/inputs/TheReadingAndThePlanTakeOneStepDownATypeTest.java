package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.WhatWasCompiled;
import souther.compiler.check.Shape;
import souther.test.RepositoryLayout;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The reading of an input and the plan for building a value take the same step down a type.
 *
 * <p>The rule {@link AnInputIsReadInOnePlaceAndNoClaimNarrowsItTest} could not state. That one holds
 * a behavior's input to one reading by counting who calls {@link InputDomain#of}, and says in its own
 * javadoc what it cannot stop: a caller making a second reading out of the same declarations. The
 * generator was that caller. It never called {@code InputDomain.of} and never had to — it worked out
 * a product's children itself, three times, and the three were kept in step by hand and were already
 * out of step about how deep to go and about how a path is spelled.
 *
 * <p><b>What this does not claim.</b> Not that the partitioning never reads a record's fields.
 * {@code Partitions.composed} does, through {@code TypeOps.fieldTypes}, to build one representative
 * value for a record — a recursion with its own reason to exist and its own way of stopping, which
 * nothing here has shown to be the same walk. What is guarded is the duplicated descent that decided
 * where a row's positions are, and the one step the two readers of that question now share.
 *
 * <p>The invariant reading is a third reader of the same step, which is why the one place is beside
 * {@code Shape} rather than in this package: what is under a type is a fact about a shape, and every
 * reader of one already looks there.
 *
 * <p>A tripwire and not a proof. The same fact is reachable by other spellings, so a helper in
 * between defeats it; what it does see is the line that has to be added first.
 */
class TheReadingAndThePlanTakeOneStepDownATypeTest {

    /** Read once: what this asks of it does not change between its checks. */
    private static final RepositoryLayout REPOSITORY = RepositoryLayout.ofWorkingDirectory();

    /** Where the fields are taken off a product shape, as the class that does it. */
    private static final String THE_ONE_PLACE = "souther.compiler.check.StructuralDescent";

    /**
     * The fields of a {@code Shape.Product} are read in one place.
     *
     * <p>Of the call and not of a spelling. What names a reader is that it asks a
     * {@link Shape.Product} for its fields, which is in its constant pool however the call was
     * written — under an import, through a variable of any name, from inside a lambda. Read as text
     * it was two guesses at once: {@code product.fields()} is a variable's name, so it answered
     * about every other type declared in products as well, and a reader that named its variable
     * something else was not there to be found.
     */
    @Test
    void theFieldsOfAProductShapeAreReadInOnePlace() throws IOException {
        List<String> readers = new ArrayList<>();
        for (String each : WhatWasCompiled.callersOf(Shape.Product.class, "fields")) {
            // The record holds its own accessor, in the members a compiler writes for every one of
            // them. Naming itself is not reading itself.
            if (!each.equals(Shape.Product.class.getName())) {
                readers.add(each);
            }
        }
        assertEquals(List.of(THE_ONE_PLACE), readers,
                "the fields of a product shape are read in one place; these read them too");
    }

    /**
     * And nothing that builds a row works the children of a product out for itself.
     *
     * <p>Asked over the package rather than of the three methods that had a descent each: a fourth
     * would be as much of a second answer as the three were, and it would be written wherever the
     * plan is held. The generator is where they were.
     */
    @Test
    void theGeneratorDoesNotDeriveProductChildrenDirectly() throws IOException {
        List<String> naming = new ArrayList<>();
        for (Path source : mainSources()) {
            if (!source.getParent().getFileName().toString().equals("partition")) {
                continue;
            }
            if (code(source).contains("Shape.Product")) {
                naming.add(where(source));
            }
        }
        assertEquals(List.of(), naming,
                "these could work out a product's children where a row is built");
    }

    private static String where(Path source) {
        return source.getParent().getFileName() + "/" + source.getFileName();
    }

    private static String code(Path source) throws IOException {
        return withoutComments(Files.readString(source, StandardCharsets.UTF_8));
    }

    /**
     * The source with its comments taken out.
     *
     * <p>Lexical and small, and deliberately not a parser. It follows string and character literals
     * so that a {@code //} inside one does not read as a comment, and it keeps what is inside them —
     * so the worst it can do is leave a comment standing, never take code away.
     */
    private static String withoutComments(String source) {
        StringBuilder out = new StringBuilder(source.length());
        int at = 0;
        while (at < source.length()) {
            char here = source.charAt(at);
            char next = at + 1 < source.length() ? source.charAt(at + 1) : '\0';
            if (here == '/' && next == '/') {
                while (at < source.length() && source.charAt(at) != '\n') {
                    at++;
                }
            } else if (here == '/' && next == '*') {
                at += 2;
                while (at + 1 < source.length()
                        && !(source.charAt(at) == '*' && source.charAt(at + 1) == '/')) {
                    at++;
                }
                at = Math.min(source.length(), at + 2);
            } else if (here == '"' || here == '\'') {
                out.append(here);
                at++;
                while (at < source.length() && source.charAt(at) != here) {
                    if (source.charAt(at) == '\\' && at + 1 < source.length()) {
                        out.append(source.charAt(at));
                        at++;
                    }
                    out.append(source.charAt(at));
                    at++;
                }
                if (at < source.length()) {
                    out.append(source.charAt(at));
                    at++;
                }
            } else {
                out.append(here);
                at++;
            }
        }
        return out.toString();
    }

    private static List<Path> mainSources() throws IOException {
        return REPOSITORY.mainJavaSources();
    }
}
