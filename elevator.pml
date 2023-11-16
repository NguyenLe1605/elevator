#define CAP 128
#define NELEVATOR 2
#define NFLOOR 4
#define START 0
#define END NFLOOR
#define EMPTY -1

// state for direction
mtype = { UP, DOWN };

// elevator state
mtype = { IDLE, RUNNING };

// state for received task
mtype = { NOT_DONE, DONE };

chan erequest = [CAP] of { mtype, int };
chan elevatorch[NELEVATOR] = [CAP] of { mtype, int};
chan finishch = [NELEVATOR] of { int };

proctype dispatcher() {
    printf("Starting dispatcher\n");
    mtype dir;
    int floor;
    int eleno;
    mtype elevator_state[NELEVATOR];
    int waiting_queue[CAP];
    int top = 0;
    int bottom = 0;
    
    int i = 0;
    for (i in elevator_state) {
        elevator_state[i] = IDLE;
    }

    for (i in waiting_queue) {
        waiting_queue[i] = EMPTY;
    }


    do 
        :: erequest ? dir, floor -> atomic { 
            printf("Receiving request from floor %d with direction %e\n", floor, dir);
            i = 0;
            do 
                :: i < NELEVATOR -> if
                                        :: elevator_state[i] == IDLE -> elevator_state[i] = RUNNING; elevatorch[i] ! NOT_DONE, floor; break
                                        :: else -> i++
                                    fi
                :: else -> {
                    waiting_queue[bottom] = floor;
                    bottom = (bottom + 1) % CAP;
                    break;
                }
            od 
        }
        :: finishch ? eleno -> atomic {
            elevator_state[eleno] = IDLE
            int task = waiting_queue[top];
            if
                :: task >= 0 -> {
                    elevator_state[eleno] = RUNNING;
                    waiting_queue[top] = EMPTY;
                    top = (top + 1) % CAP;
                    elevatorch[eleno] ! NOT_DONE, task
                }
                :: else -> skip
            fi
        }
        :: timeout -> break
    od
}

proctype elevator(int i) {
    printf("Starting elevator %d\n", i);
    int current_floor = 0;
    int floor = 0;
    do 
        :: elevatorch[i] ? _, current_floor -> atomic {
            printf("Reach passenger at floor %d from elevator %d\n", current_floor, i);
            select (floor: 0 .. NFLOOR);
            printf("Finish delivering passenger to floor %d from elevator %d\n", floor, i);
            finishch ! i
        }
        :: timeout -> break;
    od
}

proctype floor_button(int i) {
    printf("Buttons at floor %d\n", i);
    int dir = 0;
    if
        :: i == START -> dir = UP
        :: i == END -> dir = DOWN
        :: else -> select (dir: DOWN .. UP);
    fi
    erequest ! dir, i
}

init {
    run dispatcher();
    int i = 0;
    do
        :: i < NELEVATOR -> run elevator(i); i++
        :: else -> break
    od

    i = 0;
    do
        :: i < NFLOOR -> run floor_button(i); i++
        :: else -> break
    od
}
