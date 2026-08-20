package souther.compiler.source;

import java.util.Objects;

/**
 * What a compilation files one of its sources under.
 *
 * <p>Opaque, and a caller's answer: a build handing over a list gives the position in that list, a
 * workspace gives the document's URI. Nothing downstream reads a path or a name out of one — what to
 * call a file depends on which others are in front of the reader, so a renderer asks for that
 * separately.
 *
 * <p>A type rather than a {@code String}, because the slot it fills is one another kind of name fits
 * through. A module name, a display name and a message are all strings, the build keeps no parameter
 * names, and a signature saying {@code String} says nothing about which of them it wants. So a run
 * handed a module name where a source was wanted took it: {@code Compilation.ofSource(source,
 * "Main")} put {@code Main} beside positions filed under {@code 0}, and the two were paired in a
 * value for as long as nothing could tell them apart. Fifteen constructions of one compile's test
 * suite read that way.
 *
 * <p>What this does <em>not</em> say is where in the source anything is, nor whether the code a
 * position names is written there. Those travel on the position ({@code SourcePos}), which carries
 * one of these — so a value holding a position has been told which source it is in and has no reason
 * to be told a second time.
 */
public record SourceId(String value) {

    public SourceId {
        Objects.requireNonNull(value, "a source is filed under something");
        if (value.isBlank()) {
            throw new IllegalArgumentException("a source id names a source, so it is not blank");
        }
    }

    /** The id for {@code value}, or none where the caller has no source to name — a position the
     *  compiler synthesized, a module read off the module path. */
    public static SourceId orNone(String value) {
        return value == null ? null : new SourceId(value);
    }

    @Override
    public String toString() {
        return value;
    }
}
