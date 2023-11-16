#define CAP 128
#define NELEVATOR 2
#define NFLOOR 4

mtype = { UP, DOWN, IDLE };

chan dispatch = [CAP] of { int };
chan hall = [CAP] of { mtype }; 
chan numbers[NELEVATOR] = [CAP] of { int };

chan floor_start = [0] of { bool };
chan elevator_start[NELEVATOR] = [0] of { bool };
chan buttons_start[NELEVATOR] = [0] of { bool };

proctype dispatcher() {
    int queue[CAP];
    mtype direction;
    printf("======BOOTING=====\n");
    printf("Idling, starting at floor 0\n");

// Start the elevators
    int i = 0;
    do
        :: i < NELEVATOR -> { 
            run controller(i);
            elevator_start[i] ? _;
            i++;
        }
        :: else -> break;
    od

    run floor_button();
    floor_start ? _;

    printf("======END OF BOOTING======\n");
// Tell the elevator to start accepting request
    i = 0;
    do
        :: i < NELEVATOR -> { 
            elevator_start[i] ! 0;
            i++;
        }
        :: else -> break;
    od

}

proctype controller(int i) {
    int floor;
    printf("Start the elevator controller %d\n", i);

// Start the number buttons
    run number_button(i);
    buttons_start[i] ? _;

// Tell the dispatcher the elevator is ready
    elevator_start[i] ! floor;

// Wait until the whole system is ready
    elevator_start[i] ? _;
    buttons_start[i] ! 0;

// Start accepting request from the passenger
//    numbers[i] ? floor;
//    printf("Receive request at floor %d for elevator %d\n", floor, i);
}

proctype floor_button() {
    int floor;
    mtype direction = IDLE;
    
    printf("Start the floor button\n");
    floor_start ! true;
}

proctype number_button(int i) {
    int floorno;
    buttons_start[i] ! 0;
    printf("Start the buttons of the %dth elevator\n", i);

// Wait until the hall buttons is started
    buttons_start[i] ? _;

// Start sending request
    printf("Start accepting request at elevator %d\n", i);
}

init {
    atomic {
        run dispatcher();
    }
}
