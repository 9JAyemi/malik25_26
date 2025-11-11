// SVA for state_machine
// Bind this to the DUT. Focused, concise checks + coverage.

module state_machine_sva #(
  parameter int COUNT_TO_DONE = 3
)(
  input  logic        clock,
  input  logic        reset,     // active-low in DUT; assertions disable when low
  input  logic [1:0]  state_out,
  input  logic        done,
  input  logic [1:0]  state
);
  localparam logic [1:0] IDLE  = 2'b00;
  localparam logic [1:0] COUNT = 2'b01;
  localparam logic [1:0] DONES = 2'b10;

  default clocking cb @(posedge clock); endclocking
  default disable iff (!reset)

  // Helper for $past safety
  logic past_valid;
  always_ff @(posedge clock or negedge reset) begin
    if (!reset) past_valid <= 1'b0;
    else        past_valid <= 1'b1;
  end

  // While reset is asserted-low, outputs/regs must be in reset values
  assert property (@(posedge clock) !reset |-> (state==IDLE && state_out==IDLE && done==1'b0))
    else $error("Reset values incorrect");

  // No X/Z after reset deasserted
  assert property (!$isunknown({state, state_out, done}))
    else $error("X/Z detected on state/state_out/done");

  // Legal state encodings only
  assert property (state inside {IDLE, COUNT, Dones})
    else $error("Illegal state encoding");

  // IDLE must transition to COUNT next cycle
  assert property (state==IDLE |=> (state==COUNT && state_out==COUNT))
    else $error("IDLE did not go to COUNT with init state_out");

  // On first cycle in COUNT, state_out must be COUNT
  assert property (past_valid && state==COUNT && $past(state)!=COUNT |-> state_out==COUNT)
    else $error("state_out not initialized to COUNT on COUNT entry");

  // COUNT progression: increment by 1 until reaching COUNT_TO_DONE
  assert property (state==COUNT && (state_out != COUNT_TO_DONE) |=> (state==COUNT && state_out == $past(state_out)+1))
    else $error("COUNT progression increment check failed");

  // COUNT completion: when state_out == COUNT_TO_DONE, go to DONE with done=1 and state_out=DONES
  assert property (state==COUNT && (state_out == COUNT_TO_DONE) |=> (state==Dones && done && state_out==Dones))
    else $error("COUNT->DONE transition failed");

  // While in COUNT, state_out must be within [COUNT .. COUNT_TO_DONE]
  assert property (state==COUNT |-> (state_out inside {[COUNT:COUNT_TO_DONE]}))
    else $error("state_out out of range in COUNT");

  // Once in DONE, stay in DONE, with done=1 and state_out=DONES
  assert property (state==Dones |=> state==Dones)
    else $error("DONE state not sticky");
  assert property (state==Dones |-> (done && state_out==Dones))
    else $error("DONE outputs incorrect");

  // done can only be 1 in DONE, and is sticky until reset
  assert property (done |-> state==Dones)
    else $error("done asserted outside of DONE");
  assert property (done |=> done)
    else $error("done not sticky");

  // No direct IDLE->DONE jump
  assert property (past_valid && $past(state)==IDLE |-> state!=Dones)
    else $error("Illegal IDLE->DONE jump");

  // Coverage
  localparam int MAX_LAT = COUNT_TO_DONE + 2;  // deassert->DONE bound
  cover property ($rose(reset) ##[1:MAX_LAT] (state==Dones && done));
  cover property (state==COUNT && state_out==COUNT ##1
                  state==COUNT && state_out==COUNT+1 ##1
                  state==COUNT && state_out==COUNT_TO_DONE ##1
                  state==Dones && done);
  cover property (done[*3]);

endmodule

// Bind to DUT
bind state_machine state_machine_sva #(.COUNT_TO_DONE(COUNT_TO_DONE)) u_state_machine_sva (
  .clock(clock),
  .reset(reset),
  .state_out(state_out),
  .done(done),
  .state(state)
);