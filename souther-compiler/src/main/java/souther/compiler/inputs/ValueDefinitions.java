package souther.compiler.inputs;

import souther.compiler.check.AnalysisBody;
import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ElementBindings;
import souther.compiler.check.ValueTemplates;
import souther.compiler.core.Core;

import java.util.Objects;

/**
 * What the values a body builds are defined as, and what a definition is read in.
 *
 * <p>A value takes nothing and names nothing of the region that builds it, so what it is defined as
 * is one tree, held once ({@link ValueTemplates}), and it is read where nothing of any body is in
 * force: no parameter, no declared input, no dependency a row stands in for — only the bindings the
 * definition makes itself and what the operations inside it hand their closures. That is the reading
 * {@link #reading} answers with. A name given a build is read there, whichever tree the build
 * stands in and however the name was given it ({@link InputReads#meaningOf}).
 *
 * <p>The definitions are in the representation an analysis reads, where the language's operations
 * stand. So are the bindings they are read with, and the reading leaves the operations standing — a
 * reader of the tree that runs that followed a name into a definition is reading that
 * representation from there on, and never reads its nodes under its own body's names.
 *
 * <p>A value, compared by the bindings it holds. The reading is made from it when first asked and
 * kept beside it, and is no part of what it is: two equal definitions are read alike, and a reading
 * that held its definitions does not have itself among what it compares.
 */
public final class ValueDefinitions {

    /** No value is built, which is what a body that names none, or a reading of no body, holds. */
    public static final ValueDefinitions NONE = new ValueDefinitions(ElementBindings.NONE);

    private final ElementBindings definedWith;
    /** The hash of {@link #definedWith}, worked out the first time it is asked, since it is every
     *  tree the definitions hold; nought where it has not been. */
    private int hash;
    private volatile InputReads reading;

    private ValueDefinitions(ElementBindings definedWith) {
        this.definedWith = Objects.requireNonNull(definedWith,
                "a definition is read with the bindings it makes, if none");
    }

    /**
     * The definitions of the values {@code analysis} builds, read with the bindings they make —
     * or none where there is no such body.
     */
    public static ValueDefinitions of(AnalysisBody analysis, DeclarationNewtypes newtypes) {
        return analysis == null ? NONE
                : new ValueDefinitions(ElementBindings.of(analysis, newtypes));
    }

    /** The definitions {@code definedWith} holds, read with it: the bindings of a tree an analysis
     *  reads, which are those of its definitions as well. */
    public static ValueDefinitions readWith(ElementBindings definedWith) {
        return new ValueDefinitions(definedWith);
    }

    /** These and the values {@code called} builds, of a body entered where it is called. */
    ValueDefinitions and(ElementBindings called) {
        return new ValueDefinitions(definedWith.and(called));
    }

    /** What the value {@code e} is a build of is defined as, or null where it builds none held
     *  here ({@link ValueTemplates#builtBy}). */
    Core definitionOf(Core e) {
        return definedWith.templates().builtBy(e);
    }

    /** The values held here, by the name the module reaches each by. */
    public ValueTemplates templates() {
        return definedWith.templates();
    }

    /** Where a definition is read. */
    InputReads reading() {
        InputReads made = reading;
        if (made == null) {
            made = InputReads.insideADefinition(this, definedWith);
            reading = made;
        }
        return made;
    }

    @Override
    public boolean equals(Object other) {
        return this == other
                || (other instanceof ValueDefinitions that && definedWith.equals(that.definedWith));
    }

    @Override
    public int hashCode() {
        int h = hash;
        if (h == 0) {
            h = definedWith.hashCode();
            hash = h;
        }
        return h;
    }
}
