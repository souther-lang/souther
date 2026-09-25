package souther.compiler.check;

import souther.compiler.types.TypeKey;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Told of every declaration a reader was answered about, one address at a time.
 *
 * <p>For a reader whose output is a fact about which declarations it read. What a module's classes
 * were compiled against is exactly the declarations the emitter was told something about, and the
 * emitter reads them through several doors — a declaration's node, what it says, which form it is,
 * what it wraps. Each door hands its answer on through one of the {@code reading} methods, so a
 * door added later
 * is one this is told about by being a door, and not one a caller has to remember to report.
 *
 * <p>Told of what was there, where a door can tell. Asking about an address nothing declares finds
 * nothing to have been built against; a door whose answer does not say whether anything was there
 * tells of the address, and the reader decides.
 */
@FunctionalInterface
public interface DeclarationReads {

    /** A reader was answered about {@code declaration}. */
    void read(TypeKey declaration);

    /** Tells nobody. */
    DeclarationReads NOBODY = _ -> { };

    /** {@code registry}, telling this of every declaration it answers about. */
    default <D> Registry<D> readingRegistry(Registry<D> registry) {
        DeclarationReads reads = this;
        return new Registry<D>() {
            @Override
            public D declaration(TypeKey address) {
                D found = registry.declaration(address);
                if (found != null) {
                    reads.read(address);
                }
                return found;
            }

            @Override
            public boolean declares(TypeKey address) {
                boolean declared = registry.declares(address);
                if (declared) {
                    reads.read(address);
                }
                return declared;
            }

            @Override
            public Map<String, D> declaredIn(String moduleName) {
                Map<String, D> declared = registry.declaredIn(moduleName);
                for (String name : declared.keySet()) {
                    reads.read(new TypeKey(moduleName, name));
                }
                return declared;
            }

            @Override
            public List<D> inDeclarationOrder(String moduleName) {
                for (String name : registry.declaredIn(moduleName).keySet()) {
                    reads.read(new TypeKey(moduleName, name));
                }
                return registry.inDeclarationOrder(moduleName);
            }

            @Override
            public Set<String> exposedBy(String moduleName) {
                return registry.exposedBy(moduleName);
            }

            @Override
            public Set<String> moduleNames() {
                return registry.moduleNames();
            }
        };
    }

    /** {@code published}, telling this of every declaration it answers about. */
    default PublishedDeclarations readingPublished(PublishedDeclarations published) {
        return declaration -> {
            PublishedDeclarationResult said = published.of(declaration);
            if (!(said instanceof PublishedDeclarationResult.NotDeclared)) {
                read(declaration);
            }
            return said;
        };
    }

    /** {@code kinds}, telling this of every declaration it answers about. */
    default DeclarationKinds readingKinds(DeclarationKinds kinds) {
        return declaration -> {
            DeclarationKind kind = kinds.of(declaration);
            if (kind != null) {
                read(declaration);
            }
            return kind;
        };
    }

    /**
     * {@code inners}, telling this of every declaration it is asked about.
     *
     * <p>Whatever the answer. That a declaration wraps nothing is as much a fact about it as what
     * one wraps, and a reader told nothing is a reader that went on as if it were a product.
     */
    default NewtypeInners readingInners(NewtypeInners inners) {
        return declaration -> {
            read(declaration);
            return inners.of(declaration);
        };
    }
}
