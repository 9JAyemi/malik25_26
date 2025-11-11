// SVA for controller. Bind this module to the DUT and connect internal regs.
module controller_sva (
  input logic clock, reset,
  input logic run, wrSize, validIn, busy, arm,
  input logic [31:0] config_data, dataIn,
  input logic send, memoryRead, memoryWrite, memoryLastWrite,
  input logic [31:0] memoryWrData,
  input logic [2:0] state,
  input logic [17:0] counter,
  input logic [15:0] fwd, bwd
);

  // Mirror DUT encodings
  localparam logic [2:0]
    IDLE     = 3'h0,
    SAMPLE   = 3'h1,
    DELAY    = 3'h2,
    READ     = 3'h3,
    READWAIT = 3'h4;

  default clocking cb @(posedge clock); endclocking
  default disable iff (reset);

  // Basic legality and reset behavior
  assert property (state inside {IDLE,SAMPLE,DELAY,READ,READWAIT});
  assert property (@(posedge clock) reset |-> (state==IDLE && !memoryWrite && !memoryLastWrite && !memoryRead));

  // Output/register timing relationships (registered one cycle after next_*)
  assert property (memoryWrData == $past(dataIn));

  // Mutual exclusivity/sanity
  assert property (!(memoryRead && memoryWrite));
  assert property (send |-> memoryRead); // send only when memoryRead is asserted

  // Output values by previous state
  assert property ($past(state)==IDLE     |->  memoryWrite && !memoryLastWrite && !memoryRead);
  assert property ($past(state)==SAMPLE   |-> (memoryWrite == $past(validIn)) && !memoryLastWrite && !memoryRead);
  // DELAY write behavior
  assert property ($past(state)==DELAY &&  $past(validIn) && ($past(counter)!={$past(fwd),2'b11})
                   |-> memoryWrite && !memoryLastWrite && !memoryRead);
  assert property ($past(state)==DELAY &&  $past(validIn) && ($past(counter)=={$past(fwd),2'b11})
                   |-> memoryWrite &&  memoryLastWrite && !memoryRead);
  assert property ($past(state)==DELAY && !$past(validIn)
                   |-> !memoryWrite && !memoryLastWrite && !memoryRead);
  // READ cycle produces read+send pulse next cycle
  assert property ($past(state)==READ     |->  memoryRead && send && !memoryWrite && !memoryLastWrite);
  // READWAIT has all outputs low
  assert property ($past(state)==READWAIT |-> !memoryRead && !memoryWrite && !memoryLastWrite && !send);

  // memoryLastWrite only in DELAY with validIn at boundary and implies a write
  assert property (memoryLastWrite |-> ($past(state)==DELAY && $past(validIn) &&
                                        ($past(counter)=={$past(fwd),2'b11}) && memoryWrite));

  // Counter behavior
  assert property ($past(state)==IDLE   |-> counter==0);
  assert property ($past(state)==SAMPLE |-> counter==0);

  // DELAY counter increments on validIn, wraps to 0 at FWD end, holds otherwise
  assert property ($past(state)==DELAY &&  $past(validIn) && ($past(counter)!={$past(fwd),2'b11})
                   |-> counter == $past(counter)+1);
  assert property ($past(state)==DELAY &&  $past(validIn) && ($past(counter)=={$past(fwd),2'b11})
                   |-> counter == 0);
  assert property ($past(state)==DELAY && !$past(validIn)
                   |-> counter == $past(counter));

  // READ transitions and counter effects
  // If not at BWD end: go to READWAIT and increment
  assert property ($past(state)==READ && ($past(counter)!={$past(bwd),2'b11})
                   |-> (state==READWAIT) && (counter==$past(counter)+1));
  // If at BWD end: go to IDLE and clear
  assert property ($past(state)==READ && ($past(counter)=={$past(bwd),2'b11})
                   |-> (state==IDLE) && (counter==0));

  // READWAIT handshake: first cycle after READ has send=1, then it deasserts; go back to READ when !busy && !send
  assert property ($past(state)==READ && ($past(counter)!={$past(bwd),2'b11}) |-> (state==READWAIT && send));
  assert property (state==READWAIT && send |-> ##1 !send);
  assert property (state==READWAIT && !busy && !send |-> ##1 state==READ);

  // Priority/branch checks
  assert property ($past(state)==IDLE && $past(run)             |-> state==DELAY);
  assert property ($past(state)==IDLE && !$past(run) && $past(arm) |-> state==SAMPLE);
  assert property ($past(state)==SAMPLE && $past(run)           |-> state==DELAY);
  // No self-loop on READ
  assert property (state==READ |-> $past(state)!=READ);

  // Config write capture
  assert property (wrSize |=> (fwd==$past(config_data[31:16]) && bwd==$past(config_data[15:0])));

  // Coverage
  cover property (state==IDLE);
  cover property (state==SAMPLE);
  cover property (state==DELAY);
  cover property (state==READ);
  cover property (state==READWAIT);
  cover property ($past(state)==DELAY && $past(validIn) && ($past(counter)=={$past(fwd),2'b11}) ##1 state==READ);
  cover property ($past(state)==READ && ($past(counter)=={$past(bwd),2'b11}) ##1 state==IDLE);
  cover property (wrSize |=> 1'b1);

endmodule