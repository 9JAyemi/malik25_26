// SVA bind for POR
bind POR POR_sva #(.T(t)) u_por_sva (.*);

// SVA module
module POR_sva #(
  parameter int unsigned T = 10
)(
  input  VDD,
  input  CLK,
  input  reset,
  input  RESET,
  input  [1:0]  state,
  input  [31:0] counter
);
  // Encode state values (match DUT)
  localparam [1:0] IDLE=2'b00, DELAY=2'b01, NORMAL=2'b10, DEFAULT=2'b11;

  // Async reset takes effect immediately
  assert property (@(posedge reset) (state==IDLE && RESET && counter==0));

  // While reset is held, outputs/regs are held in reset state
  assert property (@(posedge CLK) reset |-> (state==IDLE && RESET && counter==0));

  // From IDLE, go to DELAY with RESET asserted and counter cleared
  assert property (@(posedge CLK) disable iff (reset)
    (state==IDLE) |=> (state==DELAY && RESET && counter==0));

  // In DELAY, counter increments by 1 while less than T; RESET stays asserted
  assert property (@(posedge CLK) disable iff (reset)
    (state==DELAY && counter < T) |=> (state==DELAY && counter == $past(counter,1,reset)+1 && RESET));

  // Counter never exceeds T while in DELAY
  assert property (@(posedge CLK) disable iff (reset)
    (state==DELAY) |-> (counter <= T));

  // Exit DELAY when counter >= T: go to NORMAL and deassert RESET next cycle
  assert property (@(posedge CLK) disable iff (reset)
    (state==DELAY && counter >= T) |=> (state==NORMAL && !RESET));

  // When in IDLE, counter clears by next cycle
  assert property (@(posedge CLK) disable iff (reset)
    (state==IDLE) |=> (counter==0));

  // RESET low only allowed in NORMAL
  assert property (@(posedge CLK) disable iff (reset)
    (!RESET) |-> (state==NORMAL));

  // NORMAL is sticky (until external reset)
  assert property (@(posedge CLK) disable iff (reset)
    (state==NORMAL) |=> (state==NORMAL && !RESET));

  // DEFAULT state must recover to IDLE next cycle (if ever reached)
  assert property (@(posedge CLK) disable iff (reset)
    (state==DEFAULT) |=> (state==IDLE));

  // No X/Z on key regs
  assert property (@(posedge CLK) !$isunknown({state, RESET, counter}));

  // Coverage: full startup sequence with programmed delay
  cover property (@(posedge CLK) disable iff (reset)
    (state==IDLE) ##1 (state==DELAY && counter==0)
      ##[T] (state==DELAY && counter==T)
      ##1 (state==NORMAL && !RESET));

  // Coverage: DEFAULT recovery path
  cover property (@(posedge CLK) disable iff (reset)
    (state==DEFAULT) ##1 (state==IDLE));

endmodule