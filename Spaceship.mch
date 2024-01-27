/* Spaceship
 * Author: Binowan Perera
 * IIT ID: 20200905
 * UoW ID: w1838855
 * Creation date: 05/01/2024
 */
/* A brief explanation about the assigned & used
 * INVARIANTS
 * can be found in the report with the Structure diagram.  
 */


MACHINE
    Spaceship
 
SETS
    OUTCOME= {Movement_Completed,Movement_Failure_Unknown_Territory, Movement_Failure_Lack_Powerunits, Move_Failed__Asteroid_Hit, Warp_Failed_Asteroid_Present, Warp_Failed_Unable_To_Warp_To_Same_Position, Spaceship_Reached_the_Starbase, Spaceship_Not_Reached_the_Starbase, Mission_Accomplished, Game_Conclude, Game_Not_Over, Start_a_New_Game};
    STATE = {Game_Won, Game_Lost, Game_not_over}
 
CONSTANTS
    SpaceAx, SpaceAy, Space, Asteroids, FreeArea, StartPoint, StarBase, MotionpowerUnits, WarpEnergy, AsteroidCollision

PROPERTIES
    SpaceAx <: NATURAL1 & SpaceAx = 1..12 & 
    SpaceAy <: NATURAL1 & SpaceAy = 1..7 &
    Space = SpaceAx * SpaceAy &
    FreeArea <: Space &
    Asteroids <: Space &
    Asteroids = {3|->2, 3|->5, 5|->4, 6|->7, 7|->1, 7|->7, 7|->5, 8|->3, 10|->6, 11|->2, 12|->5} &
    FreeArea /\ Asteroids = {} &
    FreeArea \/ Asteroids = Space &
    StarBase : FreeArea & StarBase = 6|->4 &
    StartPoint : FreeArea & StartPoint = 1|->1 &
    AsteroidCollision : NATURAL1 & AsteroidCollision = 10 &
    MotionpowerUnits : NATURAL1 & MotionpowerUnits = 5 &
    WarpEnergy : NATURAL1 & WarpEnergy = 20
 
DEFINITIONS
    //Check for asteroids being hit
    isAsteroidPresent(xx, yy) == (xx |-> yy : Asteroids);
    isWithinSpace(xx, yy) == (xx |-> yy : Space);
    isGameFinish == (xCoordinate |-> yCoordinate = StarBase) or (powerUnits < MotionpowerUnits);
    // Spaceship animation
    ANIMATION_FUNCTION == ({row,column,image | row:SpaceAy & column:SpaceAx &   
                            (IF (column |-> (8 - row) : Asteroids)
                             THEN
                                 image = 2
                             ELSE
                                 IF (column |-> row = StarBase )
                                 THEN
                                     image = 4
                                 ELSE
                                     IF (column = xCoordinate & row = 8 - yCoordinate)
                                     THEN
                                         image = 3
                                     ELSE
                                         image = 1
                                     END
                                 END
                             END)});
ANIMATION_IMG1 == "images1.gif";
    ANIMATION_IMG2== "images2.gif";
    ANIMATION_IMG3 == "images3.gif";
    ANIMATION_IMG4 == "images4.gif";
 
VARIABLES
    powerUnits,xCoordinate, yCoordinate,numberOfAsteroidCollisions, route, spaceshipExistingPosition, gameStatus
        
INVARIANT
    xCoordinate : SpaceAx &
    yCoordinate : SpaceAy &
    xCoordinate |-> yCoordinate : FreeArea &
    powerUnits : NATURAL &
    numberOfAsteroidCollisions : NATURAL &
    route : seq(FreeArea) &
    spaceshipExistingPosition : Space &
    gameStatus <: STATE 
    
INITIALISATION
    //Providing the initial stages of variables
    powerUnits := 0 ||
    numberOfAsteroidCollisions := 0 ||
    xCoordinate := 1 ||
    yCoordinate := 1 ||
    route := [StartPoint] ||
    spaceshipExistingPosition := StartPoint ||
    gameStatus := {} 
    
OPERATIONS
    //NewGame operation takes the variables to starting point
    outcome <-- NewGame (initialpowerUnits) =  
    PRE
        outcome : OUTCOME & initialpowerUnits : NATURAL & initialpowerUnits =100   
    THEN 
        powerUnits := initialpowerUnits ||
        numberOfAsteroidCollisions := 0 ||
        xCoordinate := 1 ||
        yCoordinate := 1 ||
        route := [StartPoint] ||
        spaceshipExistingPosition := StartPoint ||
        gameStatus := {Game_not_over} ||
        outcome := Start_a_New_Game 
    END;      
 
    outcome <-- MoveDown =
    PRE
        outcome : OUTCOME & not(isGameFinish)
    THEN
        IF isWithinSpace(xCoordinate, yCoordinate-1)
        THEN
            IF isAsteroidPresent(xCoordinate, yCoordinate-1)
            //Adding to the count of asteroids hit if asteroid is present in the position
            THEN
                numberOfAsteroidCollisions := numberOfAsteroidCollisions + 1 ||
                IF (powerUnits - AsteroidCollision > 0)
                THEN
                    powerUnits := powerUnits - AsteroidCollision ||
                    outcome := Move_Failed__Asteroid_Hit ||
                    gameStatus := {Game_not_over} 
                ELSE
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost} 
                END    
            ELSE
                yCoordinate := yCoordinate - 1 ||
                route := route <- (xCoordinate |-> yCoordinate - 1) ||
                spaceshipExistingPosition := (xCoordinate |-> yCoordinate - 1) ||
                
                IF (xCoordinate |-> yCoordinate-1 = StarBase )
                THEN
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Mission_Accomplished ||
                    gameStatus := {Game_Won}
                ELSIF (powerUnits - MotionpowerUnits > 0)
                THEN    
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Movement_Completed ||
                    gameStatus := {Game_not_over}
                ELSIF (powerUnits - MotionpowerUnits = 0)
                THEN    
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost}
                END    
            END    
        ELSE
            outcome :=Movement_Failure_Unknown_Territory 
        END    
    END;
   
    outcome <-- MoveUp =
    PRE
        outcome : OUTCOME & not(isGameFinish)            
    THEN
        IF isWithinSpace(xCoordinate, yCoordinate+1)
        THEN
            IF isAsteroidPresent(xCoordinate, yCoordinate+1)    
            THEN
                numberOfAsteroidCollisions := numberOfAsteroidCollisions + 1 ||
                IF (powerUnits - AsteroidCollision > 0)
                THEN
                    powerUnits := powerUnits - AsteroidCollision ||
                    outcome := Move_Failed__Asteroid_Hit ||
                    gameStatus := {Game_not_over} 
                ELSE
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost} 
                END    
            ELSE
                yCoordinate := yCoordinate + 1 ||
                route := route <- (xCoordinate |-> yCoordinate + 1) ||
                spaceshipExistingPosition := (xCoordinate |-> yCoordinate + 1) ||
                
                IF ( xCoordinate |-> yCoordinate+1 = StarBase )           
                THEN
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Mission_Accomplished ||
                    gameStatus := {Game_Won}
                ELSIF (powerUnits - MotionpowerUnits > 0)
                THEN    
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Movement_Completed ||
                    gameStatus := {Game_not_over}
                ELSIF (powerUnits - MotionpowerUnits = 0)
                THEN    
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost}
                END    
            END    
        ELSE
            outcome :=Movement_Failure_Unknown_Territory
        END    
    END;
 
    outcome <-- MoveRight=
    PRE
        outcome : OUTCOME & not(isGameFinish)
    THEN
        IF isWithinSpace(xCoordinate + 1, yCoordinate)
        THEN
            IF isAsteroidPresent(xCoordinate + 1, yCoordinate)
            THEN
                numberOfAsteroidCollisions := numberOfAsteroidCollisions + 1 ||
                IF (powerUnits - AsteroidCollision > 0)
                THEN
                    powerUnits := powerUnits - AsteroidCollision ||
                    outcome := Move_Failed__Asteroid_Hit ||
                    gameStatus := {Game_not_over} 
                ELSE
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost} 
                END    
            ELSE
                xCoordinate := xCoordinate + 1 ||
                route := route <- (xCoordinate + 1 |-> yCoordinate) ||
                spaceshipExistingPosition := (xCoordinate + 1 |-> yCoordinate) ||
                
                IF (powerUnits - MotionpowerUnits > 0)
                THEN    
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Movement_Completed ||
                    gameStatus := {Game_not_over}
                ELSIF (powerUnits - MotionpowerUnits = 0)
                THEN    
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost}
                END    
            END    
        ELSE
            outcome :=Movement_Failure_Unknown_Territory 
        END    
    END;
    
    outcome <-- MoveLeft =
    PRE
        outcome : OUTCOME & not(isGameFinish)
    THEN
        IF isWithinSpace(xCoordinate - 1, yCoordinate)
        THEN
            IF isAsteroidPresent(xCoordinate - 1, yCoordinate)
            THEN
                numberOfAsteroidCollisions := numberOfAsteroidCollisions + 1 ||
                IF (powerUnits - AsteroidCollision > 0)
                THEN
                    powerUnits := powerUnits - AsteroidCollision ||
                    outcome := Move_Failed__Asteroid_Hit ||
                    gameStatus := {Game_not_over} 
                ELSE
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost} 
                END    
            ELSE
                xCoordinate := xCoordinate - 1 ||
                route := route <- (xCoordinate - 1 |-> yCoordinate) ||
                spaceshipExistingPosition := (xCoordinate - 1 |-> yCoordinate) ||
                
                IF ( xCoordinate-1 |-> yCoordinate = StarBase )
                THEN
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Mission_Accomplished ||
                    gameStatus := {Game_Won}
                ELSIF (powerUnits - MotionpowerUnits > 0)
                THEN    
                    powerUnits := powerUnits - MotionpowerUnits ||
                    outcome := Movement_Completed ||
                    gameStatus := {Game_not_over}
                ELSIF (powerUnits - MotionpowerUnits = 0)
                THEN    
                    powerUnits := 0 ||
                    outcome := Game_Conclude ||
                    gameStatus := {Game_Lost}
                END    
            END    
        ELSE
            outcome :=Movement_Failure_Unknown_Territory 
        END    
    END;
    
    //Jumping to a free position by avoiding asteroid and current position
    outcome <-- WarpDrive(newxCoordinate, newyCoordinate) =
    PRE
        outcome : OUTCOME & newxCoordinate : NATURAL1 & newyCoordinate : NATURAL1 & not(isGameFinish)
    THEN
        IF (powerUnits >= WarpEnergy)
        THEN
            IF isWithinSpace( newxCoordinate, newyCoordinate )
            THEN
                IF (newxCoordinate = xCoordinate & newyCoordinate = yCoordinate)            
                THEN
                    outcome := Warp_Failed_Unable_To_Warp_To_Same_Position 
                ELSE
                    IF isAsteroidPresent(newxCoordinate, newyCoordinate)                
                    THEN
                        outcome := Warp_Failed_Asteroid_Present
                    ELSE
                        xCoordinate := newxCoordinate ||
                        yCoordinate := newyCoordinate ||
                        route := route <- (newxCoordinate |-> newyCoordinate) ||
                        spaceshipExistingPosition := (newxCoordinate |-> newyCoordinate) ||
                        
                        IF (newxCoordinate|->newyCoordinate = StarBase)
                        THEN
                            powerUnits := powerUnits - WarpEnergy ||
                            outcome := Mission_Accomplished ||
                            gameStatus := {Game_Won}
                        ELSIF (powerUnits - WarpEnergy > 0)
                        THEN
                            powerUnits := powerUnits - WarpEnergy ||
                            outcome := Movement_Completed ||
                            gameStatus := {Game_not_over}   
                        ELSIF (powerUnits - WarpEnergy = 0)
                        THEN
                            powerUnits := 0 ||
                            outcome := Game_Conclude ||
                            gameStatus := {Game_Lost}
                        END    
                    END    
                END    
            ELSE
                outcome :=Movement_Failure_Unknown_Territory 
            END    
        ELSE
            outcome := Movement_Failure_Lack_Powerunits 
        END    
    END;    
    
    currentPosition, currentpowerUnits, collisionCount <-- MissionStatus =
    BEGIN
        currentPosition := spaceshipExistingPosition ||
        currentpowerUnits := powerUnits ||
        collisionCount := numberOfAsteroidCollisions
    END;
    
    spaceshipRoute <-- RegionsVisited =
    BEGIN
        spaceshipRoute := route
    END;
    
    outcome <-- DockedAtStarBase =
    PRE
        outcome : OUTCOME
    THEN
        IF (spaceshipExistingPosition = StarBase)
        THEN
            outcome := Spaceship_Reached_the_Starbase
        ELSE
            outcome := Spaceship_Not_Reached_the_Starbase
        END
    END;    
    
    outcome <-- GameStatus =
    PRE
        outcome: OUTCOME & not ( spaceshipExistingPosition = StartPoint )
    THEN
        IF (spaceshipExistingPosition = StarBase)
        THEN
            outcome := Mission_Accomplished
        ELSIF (powerUnits < MotionpowerUnits) 
        THEN    
            outcome := Game_Conclude
        ELSE
            outcome := Game_Not_Over
        END
    END
             
 
END


