// contrains:
// Every request from a passenger from the floor buttons at every floor must be eventually completed
// The time to move between 2 consecutive floors is one unit of time

#define CHANNEL_CAP 128
#define ELEVATOR_CAP 7
#define NELEVATOR 2
#define NFLOOR 4
#define START 0
#define END NFLOOR - 1
#define EMPTY -1
#define TIME_UNIT 10000
#define MAX_INTERVAL 10
#define LIMIT 100

int nrequest;
int nresponse;

// elevator state
mtype = { IDLE, RUNNING };

// state for if the passenger requests the floor or not
mtype = { GO, NOT_GO }

chan erequest = [CHANNEL_CAP] of { int };
chan elevatorch[NELEVATOR] = [CHANNEL_CAP] of { int };
chan finishch = [NELEVATOR] of { int };

inline has_task(task) { task >= 0 }

inline sleep(time) {
    int tick = 0;
    do
        :: tick < time -> tick++
        :: else -> break;
    od
}

inline abs(a) {
    if
        :: a >= 0 -> skip
        :: else -> a = -a
    fi
}

inline busy_wait() {
    int time = 0;
    select(time: 0 .. MAX_INTERVAL);
    sleep(10 * time *  TIME_UNIT);
}

inline moving(src, dest) {
    int time = dest - src;
    abs(time);
    sleep(time * TIME_UNIT);
}

proctype dispatcher() {
    mtype dir;
    int floor;
    int eleno;
    mtype elevator_state[NELEVATOR];
    int waiting_queue[CHANNEL_CAP];
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
        :: erequest ? floor ->  { 
            printf("Receiving request from floor %d\n", floor);
            i = 0;
            do 
                :: i < NELEVATOR -> if
                                        :: elevator_state[i] == IDLE -> elevator_state[i] = RUNNING; elevatorch[i] ! floor; break
                                        :: else -> i++
                                    fi
                :: else -> {
                    waiting_queue[bottom] = floor;
                    bottom = (bottom + 1) % CHANNEL_CAP;
                    break;
                }
            od 
        }
        :: finishch ? eleno ->  {
            atomic {
                nresponse++;
                elevator_state[eleno] = IDLE
            }
            int task = waiting_queue[top];
            if
                :: has_task(task) -> {
                    elevator_state[eleno] = RUNNING;
                    waiting_queue[top] = EMPTY;
                    top = (top + 1) % CHANNEL_CAP;
                    elevatorch[eleno] ! task
                }
                :: else -> skip
            fi
        }
        :: timeout -> {
            assert(nresponse == nrequest);
            break;
        }
    od
}

proctype elevator(int i) {
    int current_floor = 0;
    int floor = 0;
    int dest = 0;
    do 
        :: elevatorch[i] ? dest -> {
            moving(current_floor, dest);
            atomic {
                printf("Reach passengers at floor %d from floor %d using elevator %d\n", dest, current_floor, i);
                current_floor = dest;
            }
            
            int npeople = 0
            atomic {
                select(npeople: 1 .. ELEVATOR_CAP);
                printf("There are %d passengers\n", npeople);
            }

            int cnt = 0;

            do
                :: cnt < npeople -> {
                    select (floor: START .. NFLOOR);
                    moving(current_floor, floor);
                    atomic {
                        printf("Deliver passenger to floor %d from %d using elevator %d\n", floor, current_floor, i);
                        current_floor = floor;
                        cnt++;
                    }
                }
                :: else -> break
            od

            atomic {
                printf("Finish response\n");
                finishch ! i
            }
        }
        :: timeout -> break;
    od
}


proctype request_button(int i) {
    int cnt = 0;
    do 
        :: cnt < LIMIT -> {    
            busy_wait();
            mtype state;
            select(state: NOT_GO .. GO);
            atomic {
                if
                    :: state == GO -> atomic {
                        nrequest++;
                        erequest ! i
                    }
                    :: else -> skip
                fi 
                cnt++;
            }
        }
        :: else -> break
    od
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
        :: i < NFLOOR -> run request_button(i); i++
        :: else -> break
    od
}
