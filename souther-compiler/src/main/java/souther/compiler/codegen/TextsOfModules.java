package souther.compiler.codegen;

import souther.compiler.diag.LaidOutText;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourcePos;

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
