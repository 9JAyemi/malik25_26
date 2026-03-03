// SVA checker for fsm_3bit_pattern_detection
module fsm_3bit_pattern_detection_sva (
  input logic        clk,
  input logic        reset,
  input logic [5:0]  data,
  input logic [1:0]  state,
  input logic        match
);
  localparam logic [1:0] S0=2'b00, S1=2'b01, S2=2'b10, S3=2'b11;

  default clocking cb @(posedge clk); endclocking

  // Basic sanity
  assert property (cb reset |-> (state==S0 && match==1'b0));
  assert property (cb disable iff (reset) !$isunknown(state) && !$isunknown(match));

  // One-step transition correctness
  assert property (cb disable iff (reset) (state==S0 && data[2:0]==3'b001) |=> state==S1);
  assert property (cb disable iff (reset) (state==S0 && data[2:0]!=3'b001) |=> state==S0);
  assert property (cb disable iff (reset) (state==S1 && data[2:0]==3'b010) |=> state==S2);
  assert property (cb disable iff (reset) (state==S1 && data[2:0]!=3'b010) |=> state==S0);
  assert property (cb disable iff (reset) (state==S2 && data[2:0]==3'b100) |=> state==S3);
  assert property (cb disable iff (reset) (state==S2 && data[2:0]!=3'b100) |=> state==S0);
  assert property (cb disable iff (reset) (state==S3) |=> state==S0);

  // Reverse-check next state causes (no unexpected entries)
  assert property (cb disable iff (reset) (state==S1) |-> $past(state==S0 && data[2:0]==3'b001));
  assert property (cb disable iff (reset) (state==S2) |-> $past(state==S1 && data[2:0]==3'b010));
  assert property (cb disable iff (reset) (state==S3) |-> $past(state==S2 && data[2:0]==3'b100));

  // match behavior: pulse exactly when leaving S3
  assert property (cb disable iff (reset) match == $past(state==S3));
  assert property (cb disable iff (reset) match |-> (state==S0));         // pulse occurs on S3->S0 cycle
  assert property (cb disable iff (reset) not (match && $past(match)));   // never 2+ consecutive cycles

  // End-to-end: the 001,010,100 sequence produces a match
  assert property (cb disable iff (reset)
    (state==S0 && data[2:0]==3'b001) ##1
    (state==S1 && data[2:0]==3'b010) ##1
    (state==S2 && data[2:0]==3'b100) ##1
    (state==S3) ##1
    (match && state==S0)
  );

  // End-to-end: any match must be preceded by the exact 3-step sequence
  assert property (cb disable iff (reset)
    match |-> ($past(state==S3,1) &&
               $past(state==S2,2) && $past(data[2:0]==3'b100,2) &&
               $past(state==S1,3) && $past(data[2:0]==3'b010,3) &&
               $past(state==S0,4) && $past(data[2:0]==3'b001,4))
  );

  // Coverage
  cover property (cb disable iff (reset)
    (state==S0 && data[2:0]==3'b001) ##1
    (state==S1 && data[2:0]==3'b010) ##1
    (state==S2 && data[2:0]==3'b100) ##1
    (state==S3) ##1 (match && state==S0)
  );
  cover property (cb disable iff (reset) (state==S1 && data[2:0]!=3'b010) ##1 state==S0);
  cover property (cb disable iff (reset) (state==S2 && data[2:0]!=3'b100) ##1 state==S0);
  cover property (cb disable iff (reset) $rose(match));
  cover property (cb disable iff (reset) state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);
endmodule

// Bind into the DUT
bind fsm_3bit_pattern_detection
  fsm_3bit_pattern_detection_sva sva_i (
    .clk  (clk),
    .reset(reset),
    .data (data),
    .state(state),
    .match(match)
  );