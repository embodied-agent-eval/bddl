(define (problem putting_away_Christmas_decorations_1)
    (:domain igibson)

    (:objects
     	shelf.n.01_1 - shelf.n.01
    	cabinet.n.01_1 - cabinet.n.01
    	wreath.n.01_1 wreath.n.01_2 - wreath.n.01
    	bow.n.08_1 bow.n.08_2 bow.n.08_3 bow.n.08_4 bow.n.08_5 bow.n.08_6 - bow.n.08
    	rug.n.01_1 - rug.n.01
    	ball.n.01_1 ball.n.01_2 - ball.n.01
    	wrapping.n.01_1 wrapping.n.01_2 wrapping.n.01_3 wrapping.n.01_4 wrapping.n.01_5 wrapping.n.01_6 - wrapping.n.01
    )

    (:init
        (nextto shelf.n.01_1 cabinet.n.01_1)
        (ontop wreath.n.01_1 shelf.n.01_1)
        (ontop wreath.n.01_2 shelf.n.01_1)
        (ontop bow.n.08_1 rug.n.01_1)
        (ontop bow.n.08_2 rug.n.01_1)
        (ontop bow.n.08_3 rug.n.01_1)
        (ontop bow.n.08_4 rug.n.01_1)
        (ontop bow.n.08_5 rug.n.01_1)
        (ontop bow.n.08_6 rug.n.01_1)
        (ontop ball.n.01_1 rug.n.01_1)
        (ontop ball.n.01_2 rug.n.01_1)
        (ontop wrapping.n.01_1 rug.n.01_1)
        (ontop wrapping.n.01_2 rug.n.01_1)
        (ontop wrapping.n.01_3 rug.n.01_1)
        (ontop wrapping.n.01_4 rug.n.01_1)
        (ontop wrapping.n.01_5 rug.n.01_1)
        (ontop wrapping.n.01_6 rug.n.01_1)
        (nextto rug.n.01_1 cabinet.n.01_1)
        (inroom shelf.n.01_1 garage)
        (inroom cabinet.n.01_1 garage)
        (inroom rug.n.01_1 garage)
    )

    (:goal
        (and
            (forall
                (?ball.n.01 - ball.n.01)
                (inside ?ball.n.01 ?cabinet.n.01_1)
            )
            (forall
                (?wreath.n.01 - wreath.n.01)
                (inside ?wreath.n.01 ?cabinet.n.01_1)
            )
            (forall
                (?wrapping.n.01 - wrapping.n.01)
                (inside ?wrapping.n.01 ?cabinet.n.01_1)
            )
            (forall
                (?bow.n.08 - bow.n.08)
                (inside ?bow.n.08 ?cabinet.n.01_1)
            )
        )
    )
)
