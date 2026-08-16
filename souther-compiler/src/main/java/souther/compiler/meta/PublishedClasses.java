package souther.compiler.meta;

import java.util.List;

/**
 * Where already-compiled modules are read from: a jar on the class path, the classes of a compile in
 * progress.
 *
 * <p>The input to a readback and not a part of one. What a set of classes carries is a fact about
 * those classes, true before anybody asks whether this compiler can read what they say — so it is
 * named apart from the module a readback answers with, which exists only where the reading
 * succeeded.
 *
 * <p>A known condition of the class being read is an answer and not a raise: there is no such class,
 * or there is one and the metadata this compiler needs cannot be read off it. Reading the bytes is
 * where the second is found out, and whatever reads them is the only thing that knows it — a caller
 * that had to catch would be reading an exception type as a statement about somebody's artifact,
 * which is what an artifact's failures travelling as raises cost in the first place.
 *
 * <p>A fault in an implementation of this remains a fault. What is answered is what is known about
 * the class, not everything that can go wrong on the way to it; an implementation that caught
 * whatever reached it would report a defect in this compiler as a defect in somebody's dependency,
 * which is the distinction the readback above rests on.
 */
public interface PublishedClasses {

    /** What these classes carry for {@code binaryName}. */
    Carried of(String binaryName);

    /**
     * What looking for one class found.
     *
     * <p>Three outcomes, because a class this compiler cannot read the metadata off is not a class
     * that is not there. The classes on a path came from wherever the build that made them came
     * from, and one of them may be malformed, at a major version this runtime does not know, or
     * carrying annotations that name constants nothing can make sense of. Read as an absence, an
     * author is told there is no such module while their dependency list says otherwise.
     */
    sealed interface Carried {

        /** These classes have none of that name. */
        record NoSuchClass() implements Carried {}

        /** What that class was annotated with. A class this compiler put nothing on is this, with
         *  every member absent. */
        record Declared(Declarations declarations) implements Carried {}

        /**
         * There is a class of that name and the metadata this compiler needs cannot be read off it.
         *
         * <p>Said of the metadata rather than of the class file, because that is what was asked for
         * and all that was looked at. A class file can be one the runtime reads perfectly well and
         * still carry an annotation naming a constant this compiler cannot make sense of, and a
         * reading here has no business saying anything about whether the class would load.
         */
        record UnreadableMetadata() implements Carried {}
    }

    /** {@code declarations}, or {@link Carried.NoSuchClass} where they are null — for a source of
     *  declarations that has them in hand and cannot fail to read them. */
    static Carried carrying(Declarations declarations) {
        return declarations == null ? new Carried.NoSuchClass() : new Carried.Declared(declarations);
    }

    /** What one class was annotated with. A class carries at most one of each. */
    record Declarations(SoutherModuleView module, String data, String behaviorSignature,
                        Boolean behaviorInjected) {}

    /**
     * The {@code $Module} annotation's members, as a reader here uses them.
     *
     * <p>Which module this is, is the header's to say, and it is not surfaced twice. The annotation
     * carries a {@code name} member as well — {@link ModuleMetadata} writes it, and a tool reading
     * the class file may want it — and a reading that took it as well would have three names for one
     * module: the one it was asked about, the one this member spells, and the one the header
     * declares. Two of them can disagree with the third and nothing decides which wins, so only the
     * header is read and the reading holds it against the name it was asked for.
     */
    record SoutherModuleView(int compat, String compiler, String header,
                             List<String> imports, List<String> types,
                             List<String> behaviors, List<String> invariantHelpers) {}
}
