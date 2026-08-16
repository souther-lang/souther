package souther.compiler.meta;

import java.util.List;

/**
 * Where already-compiled modules are read from: a jar on the class path, the classes of a compile in
 * progress. A name it does not know is {@code null}.
 *
 * <p>The input to a readback and not a part of one. What a set of classes carries is a fact about
 * those classes, true before anybody asks whether this compiler can read what they say — so it is
 * named apart from the module a readback answers with, which exists only where the reading
 * succeeded.
 */
public interface PublishedClasses {

    /** The declarations on {@code binaryName}'s class, or null if there is no such class. */
    Declarations of(String binaryName);

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
