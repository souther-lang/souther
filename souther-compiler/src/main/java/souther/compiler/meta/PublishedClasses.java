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
 * <p>Asking answers, and does not raise. Turning bytes into declarations is where a class file that
 * this runtime does not read is found out, and the reader that has the bytes is the only thing that
 * knows what went wrong with them: a caller that had to catch would be reading an exception type as
 * a statement about somebody's artifact, which is what an artifact's failures travelling as raises
 * cost in the first place.
 */
public interface PublishedClasses {

    /** What these classes carry for {@code binaryName}. */
    Carried of(String binaryName);

    /**
     * What looking for one class found.
     *
     * <p>Three outcomes, because a class this runtime will not read is not a class that is not
     * there. The classes on a path came from wherever the build that made them came from, and one of
     * them may be malformed or at a major version this runtime does not know. Read as an absence, an
     * author is told there is no such module while their dependency list says otherwise.
     */
    sealed interface Carried {

        /** These classes have none of that name. */
        record NoSuchClass() implements Carried {}

        /** What that class was annotated with. A class this compiler put nothing on is this, with
         *  every member absent. */
        record Declared(Declarations declarations) implements Carried {}

        /** There is a class of that name and this runtime does not read class files of its kind. */
        record NotAClassFileThisJvmReads() implements Carried {}
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
