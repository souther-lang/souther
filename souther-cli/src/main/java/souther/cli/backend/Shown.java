package souther.cli.backend;

import java.net.URI;
import java.util.regex.Pattern;

/**
 * An address or a setting as a reader is shown it: as written, but with any credentials in it
 * left out.
 *
 * <p>What a run says goes to a terminal, and from there to logs and to whoever is asked for help,
 * so a password in {@code HTTPS_PROXY}, in {@code souther.repository} or in an address a redirect
 * named is never repeated. Every address and setting a message names is shown through here, which
 * is why it is one function and not a care each message takes.
 */
public final class Shown {

    private Shown() {}

    /** The user information of an address, with or without a scheme before it. */
    private static final Pattern CREDENTIALS =
            Pattern.compile("^([A-Za-z][A-Za-z0-9+.-]*://)?[^/@\\s]*@");

    /** {@code value} with what stands before an {@code @} in its authority replaced. */
    public static String setting(String value) {
        return CREDENTIALS.matcher(value).replaceFirst("$1***@");
    }

    /** {@code uri} as written, with its user information replaced where it has any. */
    public static String address(URI uri) {
        return uri.getRawUserInfo() == null ? uri.toString() : setting(uri.toString());
    }
}
