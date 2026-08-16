package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.types.ValueName;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Where the modules a module is resolved against come from.
 *
 * <p>One question, asked by name. That is the whole of it: a universe says what it has under a name
 * and nothing about what a name written in a module means. What names mean is {@link Scoping}'s,
 * and it is the same rule whichever universe answered — a compilation reading its own sources, or a
 * reader putting a set of published classes back together.
 *
 * <p>Two universes assembling a scope apiece is what left a model that compiles in the project that
 * wrote it and refuses to be imported anywhere else: the two agreed on nothing but by having been
 * written to agree, and a rule changed on one side stayed right on the other. So there is nothing
 * here to derive a scope with. What can be worked out from a module is worked out once, where the
 * scope is assembled.
 *
 * <p>Asked one name at a time rather than handed over as a set, because a compilation that reaches
 * no other module reads none.
 */
public interface ModuleUniverse {

    /** What this universe has under {@code name}. */
    InSight module(String name);

    /**
     * What a universe has under a name.
     *
     * <p>Three answers and not two. Knowing a name and being able to read what it declares are
     * different things, and a reader told only whether a module came back cannot tell an import of
     * something that is not there — which is the importer's mistake and is reported on the import
     * line — from an import of something that is there and cannot be read, whose fault is reported
     * on its own source and would be said twice if it were said here as well.
     */
    sealed interface InSight {

        /**
         * What a universe says a module is: what it wrote, what it declares, and the library names
         * its import lines let it write bare.
         *
         * <p>One value, because none of the three can be worked out from another without deciding
         * something. The {@code import List ( map )} lines are dropped once read ({@link Exposing}),
         * so what they brought in outlives them and travels with the module or is lost — answered
         * separately it was answered emptily for a module read off the class path, and every bare
         * name in a published invariant then denoted nothing. And which declarations a module has
         * is a rule, not a reading: a name written twice keeps the first, a built-in case name is
         * refused, and what is left is what the module declares. A reader that indexed the
         * declarations itself would be a second place that rule is written, and the two would
         * differ in what they do about the ones they refuse.
         */
        record Read(Ast.Module module, Map<String, Ast.Def> declarations,
                    Map<String, ValueName.Stdlib> libraryNames) implements InSight {

            public Read {
                declarations = Collections.unmodifiableMap(new LinkedHashMap<>(declarations));
                libraryNames = Collections.unmodifiableMap(new LinkedHashMap<>(libraryNames));
            }
        }

        /** This universe has it and cannot say what it declares. Whatever is wrong with it is
         *  reported where it is, so a reader that reached it says nothing further. */
        record Unreadable() implements InSight {}

        /** Nothing of that name here. */
        record Unknown() implements InSight {}

        InSight UNREADABLE = new Unreadable();
        InSight UNKNOWN = new Unknown();

        /**
         * Whether this universe has a module of that name at all, whether or not it can say what it
         * declares.
         *
         * <p>Written once, here, because it is the one question two of the three answers agree on
         * and a reader asking it for itself asks it as "not the third one" — which reads as though
         * the other two were one answer, and is how they came to be treated as one.
         */
        default boolean isThere() {
            return !(this instanceof Unknown);
        }
    }

    /**
     * The modules of a set already read. A name that is not among them is nothing this universe
     * has — a reading that went wrong is left out by whoever read it, and is
     * {@link InSight.Unreadable} only if it says so.
     *
     * <p>A record rather than a lambda, for the reason {@link Scoping.OfTheUniverse} is: a universe
     * ends up inside an answer a compilation remembers, and two answers built from the same
     * universe have to be equal or nothing that read one is ever kept.
     */
    record OfWhatIsRead(Map<String, InSight> modules) implements ModuleUniverse {

        public OfWhatIsRead {
            modules = Map.copyOf(modules);
        }

        @Override
        public InSight module(String name) {
            return modules.getOrDefault(name, InSight.UNKNOWN);
        }
    }

    /** Nothing in sight — a module resolved on its own. */
    ModuleUniverse NOTHING = new OfWhatIsRead(Map.of());
}
