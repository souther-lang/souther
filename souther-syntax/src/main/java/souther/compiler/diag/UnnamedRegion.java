package souther.compiler.diag;

/**
 * A stretch of a text this compilation cannot name: a real line and a real column, of a text whose
 * identity was never given.
 *
 * <p>The counterpart of {@link DiagnosticPlace.InSource}, and the reason both exist as types rather
 * than as regions somebody checked. That one refuses a region that does not name a source; this one
 * refuses a region that does. So a value holding a source identity beside one of these is not
 * holding two answers to one question — this says, in the type, that it has no answer of its own —
 * and a value holding one beside the other would be, which is what the check written for #760 is
 * about.
 *
 * <p>Which text it is remains somebody's to say, and it is said where the report is shown rather
 * than where it was found: an editor holding an unsaved buffer knows which document it is looking
 * at, and the parse that read that buffer did not ({@link Citation.Unplaced}). That is a state a
 * compile has and not one left over from a compile, so what a report built over such a text carries
 * is this, and the identity arrives beside it at the surface ({@link Spot.InTextBeingRead}).
 *
 * <p>Code copied in from elsewhere is admitted too ({@link Citation.UnplacedElsewhere}): a body
 * spliced into a buffer is still a stretch of that buffer, and where the code came from is a
 * separate question that {@link Diagnostic#whereItsCodeIsWritten()} answers. Refusing it here would
 * put a splice into a buffer somewhere neither type covers.
 */
public record UnnamedRegion(Region region) {

    public UnnamedRegion {
        OnePlace.heldTo(region);
        switch (Citation.of(region.start())) {
            case Citation.Unplaced _, Citation.UnplacedElsewhere _ -> { }
            case Citation.Written _, Citation.Reached _, Citation.OutOfSight _ ->
                    throw new NotInAnUnnamedText(
                            "this region is in a text something can name, so a source identity"
                                    + " beside it would be a second answer: " + region);
        }
    }

    /**
     * A region that is in a text something already names, handed over as one that is not.
     *
     * <p>The whole of what this type is for. A region in a text something can name, held as one that
     * cannot, is a value with a source identity beside it and a declaration that it has none — two
     * answers to one question, which is what holding these apart at the type was meant to stop.
     */
    public static final class NotInAnUnnamedText extends IllegalArgumentException {

        private static final long serialVersionUID = 1L;

        NotInAnUnnamedText(String message) {
            super(message);
        }
    }
}
