
(:goal 
    (and 
        (forn 
            (4) 
                (?pack - pack) 
                (and 
                    (forpairs 
                        (?water - water) 
                        (?bottle - bottle) 
                        (and 
                            (inside ?water ?bottle) 
                            (inside ?bottle ?pack) 
                            (not 
                                (open ?bottle)
                            )
                        )
                    ) 
                    (fornpairs 
                        (4) 
                            (?bag - bag) 
                            (?sandwich - sandwich) 
                            (and 
                                (inside ?sandwich ?bag) 
                                (inside ?bag ?pack) 
                                (not 
                                    (open ?bag)
                                )
                            )
                        ) 
                        (fornpairs 
                            (4) 
                                (?bag - bag) 
                                (?cookie - cookie) 
                                (and 
                                    (inside ?cookie ?bag) 
                                    (inside ?bag ?pack) 
                                    (not 
                                        (open ?bag)
                                    )
                                )
                            )
                        )
                    ) 
                    (fornpairs 
                        (4) 
                            (?pack - pack) 
                            (?napkin - napkin) 
                            (inside ?napkin ?pack)
                        ) 
                        (fornpairs 
                            (4) 
                                (?pack - pack) 
                                (?edible_fruit - edible_fruit) 
                                (inside ?edible_fruit ?pack)
                            ) 
                            (fornpairs 
                                (4) 
                                    (?pack - pack) 
                                    (?muffin - muffin) 
                                    (inside ?muffin ?pack)
                                ) 
                                (forall 
                                    (?pack - pack) 
                                    (and 
                                        (ontop ?pack ?counter1) 
                                        (not 
                                            (open ?pack)
                                        )
                                    )
                                )
                            )
                        )