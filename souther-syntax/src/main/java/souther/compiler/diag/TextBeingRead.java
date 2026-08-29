package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.Objects;
import java.util.Optional;

/**
 * The text a surface is showing a report from, as that surface names it.
 *
 * <p>A report found in a text this compilation cannot name has a real line and a real column and no
 * file ({@link Citation.Unplaced}). Which text those numbers are of is not the report's to say and
 * is not lost either: an editor holding an unsaved buffer knows which document it is looking at, and
 * a caller that parsed a snippet is holding the snippet. This is that answer, given where the report
 * is shown rather than where it was found.
 *
 * <p>Two arms because there are two ways a surface has a text. A compile, a build and an editor
 * identify their sources, and hand over the identity; a caller with a text and no identity for it
 * hands over the text. Neither is the other's default: a resolver asked for an identity nobody gave
 * answers nothing, and that is what put a report's numbers in front of whichever file was to hand.
 *
 * <p>An identity where there is one, so that a place in a named text and a place in the same text
 * shown by name can be seen to be one place ({@link Spot#knownToBeOneText}). Where there is none,
 * two places cannot be shown to be one and are not treated as one — which is the honest answer and
 * not a claim that they differ.
 */
public sealed interface TextBeingRead {

    /** The identity this text is under, where the surface has one to compare. */
    Optional<SourceId> identity();

    /** A text the surface names — a source of a compile, a document in an editor. */
    record UnderAnId(SourceId source) implements TextBeingRead {

        public UnderAnId {
            Objects.requireNonNull(source, "a text named by an identity has one");
        }

        @Override
        public Optional<SourceId> identity() {
            return Optional.of(source);
        }
    }

    /** A text the surface is holding and has no identity for — a snippet somebody parsed. What is
     *  handed over is what to quote from and what to call it. */
    record AsHandedOver(SourceContext text) implements TextBeingRead {

        public AsHandedOver {
            Objects.requireNonNull(text, "a text handed over is a text");
        }

        @Override
        public Optional<SourceId> identity() {
            return Optional.empty();
        }
    }
}
