package souther.compiler.codegen;

import souther.compiler.diag.LaidOutText;
import souther.compiler.diag.PhysicalPos;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourcePos;

import java.util.Objects;
import java.util.Optional;

/**
 * The texts a code generator is handed, able to say how each is laid out and which module each is
 * part of.
 *
 * <p>Two questions about one text, and a generator needs both where what it emits is data about a
 * place rather than an entry of a class's line table. A line table names one text, the class's own;
 * a construction's site is the place it is written, which for a body inlined from another module is
 * a place in that module's text, and is said as that module and the line and column in that text.
 */
public interface TextsOfModules extends SourceLayouts {

    /** The module {@code text} is part of, or empty where this holds no such text. */
    Optional<String> moduleOf(QuotedFrom text);

    /**
     * Where {@code place} is written: the module of the text it is quoted from, and where it sits
     * in that text, where this holds it laid out.
     *
     * <p>The one place a place in the source is said as a module and a place in its text, for the
     * code generator that writes it into a run and for every reader that holds what a run said to
     * a place a finding names. None where the place has no text, its text is no module's this
     * knows, or the text is not laid out: a place said as another module's, or as a module with no
     * line, would be a place the reader is told and nothing is written at.
     */
    default Optional<WrittenAt> writtenAt(SourcePos place) {
        if (place == null) {
            return Optional.empty();
        }
        Optional<String> module = moduleOf(place.quotedFrom());
        PhysicalPos sits = module.isEmpty() ? null : resolve(place);
        return sits == null ? Optional.empty() : Optional.of(new WrittenAt(module.get(), sits));
    }

    /**
     * A place as {@link #writtenAt} says it.
     *
     * @param module the module whose text the place is in
     * @param sits   where it sits in that text
     */
    record WrittenAt(String module, PhysicalPos sits) {

        public WrittenAt {
            Objects.requireNonNull(module, "a place is in some module's text");
            Objects.requireNonNull(sits, "a place sits somewhere in its text");
        }
    }

    /** One that holds nothing — for a caller with no texts to hand over. */
    TextsOfModules NONE = new TextsOfModules() {

        @Override
        public LaidOutText of(SourcePos place) {
            return null;
        }

        @Override
        public Optional<String> moduleOf(QuotedFrom text) {
            return Optional.empty();
        }
    };
}
