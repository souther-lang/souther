package souther.lsp.transport;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.UncheckedIOException;
import java.nio.charset.StandardCharsets;

/**
 * The LSP base protocol transport: {@code Content-Length}-framed JSON messages over a byte stream
 * (typically stdio). The one subtle rule is that the length is a count of UTF-8 <em>bytes</em>, not
 * characters — a Japanese identifier makes the two differ — so framing is done at the byte level and
 * the JSON payload is decoded/encoded as UTF-8 exactly once, here.
 */
public final class MessageConnection {

    /** The largest message body read; the length comes off the wire, so it is bounded before it sizes a buffer. */
    static final int MAX_MESSAGE_BYTES = 64 * 1024 * 1024;

    /** The longest header line read. */
    static final int MAX_HEADER_LINE_CHARS = 8 * 1024;

    private final InputStream in;
    private final OutputStream out;

    public MessageConnection(InputStream in, OutputStream out) {
        this.in = in;
        this.out = out;
    }

    /** Reads one framed message and returns its JSON body, or {@code null} at end of input. */
    public String read() {
        try {
            int contentLength = -1;
            while (true) {
                String line = readHeaderLine();
                if (line == null) {
                    return null;   // end of input
                }
                if (line.isEmpty()) {
                    break;         // the blank line terminates the header block
                }
                int colon = line.indexOf(':');
                if (colon >= 0 && line.substring(0, colon).trim().equalsIgnoreCase("Content-Length")) {
                    contentLength = parseContentLength(line.substring(colon + 1).trim());
                }
            }
            if (contentLength < 0) {
                throw new IllegalStateException("message header had no Content-Length");
            }
            byte[] body = readExactly(contentLength);
            return new String(body, StandardCharsets.UTF_8);
        } catch (IOException e) {
            throw new UncheckedIOException("failed to read an LSP message", e);
        }
    }

    /** Writes one framed message. Synchronized so a response and a server notification never interleave. */
    public synchronized void write(String json) {
        byte[] body = json.getBytes(StandardCharsets.UTF_8);
        byte[] header = ("Content-Length: " + body.length + "\r\n\r\n")
                .getBytes(StandardCharsets.US_ASCII);
        try {
            out.write(header);
            out.write(body);
            out.flush();
        } catch (IOException e) {
            throw new UncheckedIOException("failed to write an LSP message", e);
        }
    }

    /** Reads one header line up to and including {@code \n}, returned without the trailing CRLF;
     * {@code null} at end of input before any byte. */
    private String readHeaderLine() throws IOException {
        StringBuilder sb = new StringBuilder();
        int c = in.read();
        if (c == -1) {
            return null;
        }
        int consumed = 0;   // what was read, a carriage return included, and not only what is kept
        while (c != -1 && c != '\n') {
            if (++consumed > MAX_HEADER_LINE_CHARS) {
                throw new IllegalStateException("message header line is longer than " + MAX_HEADER_LINE_CHARS);
            }
            if (c != '\r') {
                sb.append((char) c);
            }
            c = in.read();
        }
        return sb.toString();
    }

    private static int parseContentLength(String value) {
        int length;
        try {
            length = Integer.parseInt(value);
        } catch (NumberFormatException e) {
            throw new IllegalStateException("Content-Length is not a number: " + value, e);
        }
        if (length < 0 || length > MAX_MESSAGE_BYTES) {
            throw new IllegalStateException("Content-Length " + length + " is outside 0.." + MAX_MESSAGE_BYTES);
        }
        return length;
    }

    private byte[] readExactly(int n) throws IOException {
        // Grown as the bytes arrive: the length is the sender's claim, and a buffer of that size is
        // not allocated for a body that never comes.
        byte[] buf = in.readNBytes(n);
        if (buf.length < n) {
            throw new IllegalStateException("stream ended mid-message: wanted " + n
                    + " bytes, got " + buf.length);
        }
        return buf;
    }
}
