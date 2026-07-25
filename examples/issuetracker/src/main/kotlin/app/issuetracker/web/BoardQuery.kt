// The read side. countByLabel and topLabels are pure behaviors over a whole Board, so something has to
// assemble that Board from storage — and unlike a label change, a summary makes no decision that the
// domain needs to be in on. So it is not an injected behavior: the boundary reads the rows and builds
// the Board through the derived decoder, then hands it to the pure behavior.
package app.issuetracker.web

import app.issuetracker.issueRows
import app.issuetracker.souther.decodeOrFail

import example.issuetracker.Board

import org.jooq.DSLContext
import org.springframework.stereotype.Component

@Component
class BoardQuery(private val dsl: DSLContext) {

    /** Every stored issue as one Board. */
    fun board(): Board = Board.decoder().decodeOrFail(mapOf("issues" to dsl.issueRows()))
}
