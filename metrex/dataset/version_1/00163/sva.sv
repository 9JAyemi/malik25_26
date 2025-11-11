// SVA for quadrature_decoder
// Bindable, concise, strong checks and useful coverage.

module quadrature_decoder_sva (
  input  logic        CLOCK,
  input  logic        RESET,
  input  logic        A,
  input  logic        B,
  input  logic        COUNT_ENABLE,
  input  logic        DIRECTION,
  input  logic [3:0]  SPEED
);

  default clocking cb @(posedge CLOCK); endclocking

  // Convenience functions (safe $past defaults under reset)
  let CE  = ($past(A,1,1'b0) ^ $past(A,2,1'b0) ^ $past(B,1,1'b0) ^ $past(B,2,1'b0));
  let DIR = ($past(A,1,1'b0) ^ $past(B,2,1'b0));

  // Asynchronous reset drives outputs low immediately and while asserted
  assert property (@(posedge RESET) (COUNT_ENABLE==0 && DIRECTION==0 && SPEED==0));
  assert property (@cb RESET |-> (COUNT_ENABLE==0 && DIRECTION==0 && SPEED==0));

  // COUNT_ENABLE is an exact one-shot of CE
  assert property (@cb disable iff (RESET)
                   COUNT_ENABLE == (CE && !$past(COUNT_ENABLE,1,1'b0)));
  assert property (@cb disable iff (RESET)
                   COUNT_ENABLE |=> !COUNT_ENABLE);

  // DIRECTION is an exact one-shot of DIR
  assert property (@cb disable iff (RESET)
                   DIRECTION == (DIR && !$past(DIRECTION,1,1'b0)));
  assert property (@cb disable iff (RESET)
                   DIRECTION |=> !DIRECTION);

  // SPEED constraints
  assert property (@cb disable iff (RESET) SPEED inside {[4'd0:4'd27]}); // 0..27
  // No change without an event
  assert property (@cb disable iff (RESET) !CE |-> SPEED == $past(SPEED,1,SPEED));
  // Step size at most 1
  assert property (@cb disable iff (RESET)
                   (SPEED == $past(SPEED,1,SPEED)) ||
                   (SPEED == $past(SPEED,1,SPEED)+1) ||
                   (SPEED+1 == $past(SPEED,1,SPEED)));
  // If SPEED changes, it must match direction of the event
  assert property (@cb disable iff (RESET)
                   (SPEED == $past(SPEED)+1) |-> (CE && DIR));
  assert property (@cb disable iff (RESET)
                   (SPEED+1 == $past(SPEED)) |-> (CE && !DIR));
  // Saturation at boundaries
  assert property (@cb disable iff (RESET)
                   (SPEED==27 && CE && DIR) |=> SPEED==27);
  assert property (@cb disable iff (RESET)
                   (SPEED==0  && CE && !DIR) |=> SPEED==0);

`ifdef ASSUME_QUAD_ENV
  // Optional environment constraint: Gray transitions (at most one toggles per cycle)
  assume property (@cb disable iff (RESET)
                   ((A != $past(A,1,A)) || (B != $past(B,1,B))) |->
                   ((A != $past(A,1,A)) ^  (B != $past(B,1,B))));
`endif

  // Coverage
  cover property (@cb disable iff (RESET) CE && DIR);        // increment event
  cover property (@cb disable iff (RESET) CE && !DIR);       // decrement event
  cover property (@cb disable iff (RESET) SPEED==0  ##[1:$] SPEED==27); // climb to max
  cover property (@cb disable iff (RESET) SPEED==27 ##[1:$] SPEED==0);  // descend to min
  // Typical quadrature step sequences (CW/CCW)
  sequence s_cw;  (A==0 && B==0) ##1 (A==0 && B==1) ##1 (A==1 && B==1) ##1 (A==1 && B==0) ##1 (A==0 && B==0); endsequence
  sequence s_ccw; (A==0 && B==0) ##1 (A==1 && B==0) ##1 (A==1 && B==1) ##1 (A==0 && B==1) ##1 (A==0 && B==0); endsequence
  cover property (@cb disable iff (RESET) s_cw);
  cover property (@cb disable iff (RESET) s_ccw);

endmodule

// Bind into the DUT
bind quadrature_decoder quadrature_decoder_sva sva (
  .CLOCK(CLOCK),
  .RESET(RESET),
  .A(A),
  .B(B),
  .COUNT_ENABLE(COUNT_ENABLE),
  .DIRECTION(DIRECTION),
  .SPEED(SPEED)
);