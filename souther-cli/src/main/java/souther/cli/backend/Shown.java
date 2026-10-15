package souther.cli.backend;

import java.net.URI;
import java.net.URISyntaxException;

/**
 * An address as a reader is shown it.
 *
 * <p>What a run says goes to a terminal, and from there to logs and to whoever is asked for help,
 * so nothing is shown as it was written or served: a setting or a header that did not read as an
 * address is not shown at all, and one that did is shown as built again from the parts it was read
 * into — its scheme, host, port and path — so its credentials, and anything else in it, are not
 * repeated. Masking what was written instead would have to foresee every way it can be written.
 */
public final class Shown {

    private Shown() {}

    /** {@code uri} built again from its scheme, host, port and path. */
    public static String address(URI uri) {
        try {
            return new URI(uri.getScheme(), null, uri.getHost(), uri.getPort(), uri.getPath(),
                    null, null).toString();
        } catch (URISyntaxException e) {
            return uri.getScheme() + "://" + uri.getHost();
        }
    }
}
