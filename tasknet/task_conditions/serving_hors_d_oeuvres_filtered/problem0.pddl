(define (problem serving_hors_d_oeuvres_0)
    (:domain igibson)

    (:objects
     	chip1 chip10 chip11 chip12 chip13 chip14 chip15 chip16 chip17 chip18 chip19 chip2 chip20 chip21 chip22 chip23 chip24 chip3 chip4 chip5 chip6 chip7 chip8 chip9 - chip
    	fridge1 - fridge
    	tray1 tray2 tray3 tray4 - tray
    	counter1 - counter
    	plate1 plate10 plate11 plate12 plate13 plate14 plate15 plate16 plate17 plate18 plate19 plate2 plate20 plate21 plate22 plate23 plate24 plate3 plate4 plate5 plate6 plate7 plate8 plate9 - plate
    	cabinet1 - cabinet
    	table1 table2 - table
    )
    
    (:init 
        (inside chip1 fridge1) 
        (inside chip2 fridge1) 
        (inside chip3 fridge1) 
        (inside chip4 fridge1) 
        (inside chip5 fridge1) 
        (inside chip6 fridge1) 
        (inside chip7 fridge1) 
        (inside chip8 fridge1) 
        (inside chip9 fridge1) 
        (inside chip10 fridge1) 
        (inside chip11 fridge1) 
        (inside chip12 fridge1) 
        (inside chip13 fridge1) 
        (inside chip14 fridge1) 
        (inside chip15 fridge1) 
        (inside chip16 fridge1) 
        (inside chip17 fridge1) 
        (inside chip18 fridge1) 
        (inside chip19 fridge1) 
        (inside chip20 fridge1) 
        (inside chip21 fridge1) 
        (inside chip22 fridge1) 
        (inside chip23 fridge1) 
        (inside chip24 fridge1) 
        (ontop tray1 counter1) 
        (ontop tray2 counter1) 
        (ontop tray3 counter1) 
        (ontop tray4 counter1) 
        (inside plate1 cabinet1) 
        (inside plate2 cabinet1) 
        (inside plate3 cabinet1) 
        (inside plate4 cabinet1) 
        (inside plate5 cabinet1) 
        (inside plate6 cabinet1) 
        (inside plate7 cabinet1) 
        (inside plate8 cabinet1) 
        (inside plate9 cabinet1) 
        (inside plate10 cabinet1) 
        (inside plate11 cabinet1) 
        (inside plate12 cabinet1) 
        (inside plate13 cabinet1) 
        (inside plate14 cabinet1) 
        (inside plate15 cabinet1) 
        (inside plate16 cabinet1) 
        (inside plate17 cabinet1) 
        (inside plate18 cabinet1) 
        (inside plate19 cabinet1) 
        (inside plate20 cabinet1) 
        (inside plate21 cabinet1) 
        (inside plate22 cabinet1) 
        (inside plate23 cabinet1) 
        (inside plate24 cabinet1) 
        (inroom counter1 kitchen) 
        (inroom fridge1 kitchen) 
        (inroom table1 living_room) 
        (inroom table2 living_room) 
        (inroom cabinet1 kitchen)
    )
    
    (:goal 
        (and 
            (forall 
                (?tray - tray) 
                (fornpairs 
                    (6) 
                    (?chip - chip) 
                    (?plate - plate) 
                    (and 
                        (ontop ?chip ?plate) 
                        (ontop ?plate ?tray)
                    )
                )
            ) 
            (forpairs 
                (?tray - tray) 
                (?table - table) 
                (ontop ?tray ?table)
            )
        )
    )
)
