// SVA checker for controlrecorder
// Bind this to the DUT instance
module controlrecorder_sva #(parameter [25:0] MAXCYC = 26'b10111110101111000001111111)
(
  input logic clock,
  input logic reset
);
  // Mirror state encodings (must match DUT)
  localparam STATIONARY           = 3'b000;
  localparam START_RECORD         = 3'b001;
  localparam RECORDING            = 3'b010;
  localparam WAITING_FOR_PLAYBACK = 3'b011;
  localparam START_PLAYBACK       = 3'b100;
  localparam PLAYBACK             = 3'b101;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!reset);

  // Reset behavior (active-low)
  assert property (@(posedge clock) !reset |-> (current_state==STATIONARY && num_keys==0 && cyclecounter==0 && cell_number==0 && mode==2'b00));

  // Legal state encodings
  assert property (current_state inside {STATIONARY,START_RECORD,RECORDING,WAITING_FOR_PLAYBACK,START_PLAYBACK,PLAYBACK});
  assert property (next_state    inside {STATIONARY,START_RECORD,RECORDING,WAITING_FOR_PLAYBACK,START_PLAYBACK,PLAYBACK});

  // Pipeline relation between next_state and current_state
  assert property ($past(reset) |-> current_state == $past(next_state));

  // Mode mapping
  assert property ((current_state==RECORDING) |-> mode==2'b01);
  assert property ((current_state==PLAYBACK)  |-> mode==2'b10);
  assert property ((current_state!=RECORDING && current_state!=PLAYBACK) |-> mode==2'b00);

  // STATIONARY transitions
  assert property (current_state==STATIONARY |-> next_state == (go ? START_RECORD : STATIONARY));

  // START_RECORD effects and transition
  assert property (current_state==START_RECORD |=> (next_state==RECORDING && cyclecounter==0 && num_keys==0 && cell_number==0));

  // RECORDING: when full (num_keys==31) -> go wait (and clear counters)
  assert property ((current_state==RECORDING && num_keys==5'd31) |=> (next_state==WAITING_FOR_PLAYBACK && cyclecounter==0 && cell_number==0));

  // RECORDING: key change -> capture, bump counters, keep recording
  assert property ((current_state==RECORDING && num_keys!=5'd31 && (prev_keys!=keys))
                   |=> (num_keys==$past(num_keys)+1 && cyclecounter==0 && cell_number==$past(cell_number)+1 && next_state==RECORDING));

  // RECORDING: hold and not at MAX -> cyclecounter increments only
  assert property ((current_state==RECORDING && num_keys!=5'd31 && (prev_keys==keys) && (cyclecounter!=MAXCYC))
                   |=> (cyclecounter==$past(cyclecounter)+1 && cell_number==$past(cell_number) && next_state==RECORDING));

  // RECORDING: hold and at MAX -> wrap counter, bump cell_number
  assert property ((current_state==RECORDING && num_keys!=5'd31 && (prev_keys==keys) && (cyclecounter==MAXCYC))
                   |=> (cyclecounter==0 && cell_number==$past(cell_number)+1 && next_state==RECORDING));

  // WAITING_FOR_PLAYBACK transitions
  assert property (current_state==WAITING_FOR_PLAYBACK |-> next_state == (go ? WAITING_FOR_PLAYBACK : START_PLAYBACK));

  // START_PLAYBACK effects and transition
  assert property (current_state==START_PLAYBACK |=> (next_state==PLAYBACK && countdown_register==countdown && i==0 && cell_number==0));

  // PLAYBACK: countdown running -> decrement, stay in PLAYBACK
  assert property ((current_state==PLAYBACK && countdown_register!=0) |=> (countdown_register==$past(countdown_register)-1 && next_state==PLAYBACK));

  // PLAYBACK: countdown hit 0 and more events -> load, advance i, bump cell_number, drive prev_keys
  assert property ((current_state==PLAYBACK && countdown_register==0 && i < num_keys)
                   |=> (i==$past(i)+1 && countdown_register==countdown && cell_number==$past(cell_number)+1
                        && next_state==PLAYBACK && prev_keys==$past(keystrokes[$past(i)])));

  // PLAYBACK: done -> return to STATIONARY
  assert property ((current_state==PLAYBACK && countdown_register==0 && i==num_keys) |=> (next_state==STATIONARY));

  // Stability outside states that write these regs
  assert property ($past(reset) && !($past(current_state inside {START_RECORD,RECORDING})) |-> cyclecounter==$past(cyclecounter));
  assert property ($past(reset) && !($past(current_state inside {START_PLAYBACK,PLAYBACK})) |-> (countdown_register==$past(countdown_register) && i==$past(i)));

  // num_keys only increases on key change in RECORDING
  assert property ((num_keys==$past(num_keys)+1) |-> ($past(current_state)==RECORDING && $past(prev_keys!=keys) && $past(num_keys!=5'd31)));

  // prev_keys only updates during PLAYBACK step when emitting a key
  assert property ((prev_keys!=$past(prev_keys)) |-> ($past(current_state)==PLAYBACK && $past(countdown_register==0) && $past(i < num_keys)));

  // -------------- Coverage --------------

  // Visit all states
  cover property (current_state==STATIONARY);
  cover property (current_state==START_RECORD);
  cover property (current_state==RECORDING);
  cover property (current_state==WAITING_FOR_PLAYBACK);
  cover property (current_state==START_PLAYBACK);
  cover property (current_state==PLAYBACK);

  // Record path: go -> START_RECORD -> RECORDING
  cover property (current_state==STATIONARY && go ##1 current_state==START_RECORD ##1 current_state==RECORDING);

  // Capture at least two key changes during RECORDING
  cover property (current_state==RECORDING && (prev_keys!=keys)
                  ##1 current_state==RECORDING && (prev_keys!=keys));

  // Record completion (num_keys==31) -> wait
  cover property (current_state==RECORDING && num_keys==5'd31 ##1 current_state==WAITING_FOR_PLAYBACK);

  // Playback path: wait with !go -> start -> playback -> at least one emit
  cover property (current_state==WAITING_FOR_PLAYBACK && !go
                  ##1 current_state==START_PLAYBACK
                  ##1 current_state==PLAYBACK && countdown_register==0 && i < num_keys);

  // Playback done -> STATIONARY
  cover property (current_state==PLAYBACK && countdown_register==0 && i==num_keys ##1 current_state==STATIONARY);

  // cyclecounter wrap event in RECORDING
  cover property (current_state==RECORDING && prev_keys==keys && cyclecounter==MAXCYC
                  ##1 cyclecounter==0 && cell_number==$past(cell_number)+1);
endmodule

// Bind into DUT
bind controlrecorder controlrecorder_sva #(.MAXCYC(26'b10111110101111000001111111))
  controlrecorder_sva_i(.clock(clock), .reset(reset));