// SVA for pulse_gen
module pulse_gen_sva (
    input  logic        CLK,
    input  logic        RST,
    input  logic        START,
    input  logic [15:0] DURATION,
    input  logic        PULSE,
    input  logic [15:0] count
);
  default clocking cb @(posedge CLK); endclocking

  // X-checks (skip during reset)
  assert property (disable iff (RST) !$isunknown({PULSE, count}));

  // Reset clears state on next cycle
  assert property (@(posedge CLK) RST |=> (count==16'd0 && PULSE==1'b0));

  // When START=0, outputs clear on next cycle
  assert property (disable iff (RST) !START |=> (count==16'd0 && PULSE==1'b0));

  // Active counting step
  assert property (disable iff (RST)
                   START && (count < DURATION) |=> (count == $past(count)+16'd1 && PULSE==1'b1));

  // End-of-burst/reset step (also covers DURATION==0 case)
  assert property (disable iff (RST)
                   START && (count >= DURATION) |=> (count==16'd0 && PULSE==1'b0));

  // Pulse causality: a 1 on PULSE comes from prior START and count<DURATION
  assert property (disable iff (RST)
                   PULSE |-> ($past(START) && $past(count < DURATION)));

  // When PULSE is 1, count must be non-zero (first high cycle sets count to 1)
  assert property (disable iff (RST) PULSE |-> (count > 16'd0));

  // Explicitly enforce idle for zero duration
  assert property (disable iff (RST) START && (DURATION==16'd0) |=> (count==16'd0 && PULSE==1'b0));

  // Coverage: reset, zero-duration, one burst, and restart under held START
  cover property (@(posedge CLK) RST ##1 (count==16'd0 && !PULSE));
  cover property (disable iff (RST) START && (DURATION==16'd0) ##1 (!PULSE && count==16'd0) [*2]);

  // Cover one complete high burst then low (DURATION held for the burst)
  cover property (disable iff (RST)
    START && (DURATION>16'd0) && (count==16'd0)
    ##1 (PULSE && count==16'd1) [* (DURATION-16'd1)]
    ##1 (!PULSE && count==16'd0)
  );

  // Cover restart of next burst when START is held high
  cover property (disable iff (RST)
    START && (DURATION>16'd0) && (count==16'd0)
    ##1 (PULSE && count==16'd1) [* (DURATION-16'd1)]
    ##1 (!PULSE && count==16'd0)
    ##1 (START && PULSE)
  );

endmodule

// Bind into the DUT
bind pulse_gen pulse_gen_sva u_pulse_gen_sva (
  .CLK(CLK),
  .RST(RST),
  .START(START),
  .DURATION(DURATION),
  .PULSE(PULSE),
  .count(count)
);