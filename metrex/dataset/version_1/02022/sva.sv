// SVA for fsm_bit_pattern_detection
bind fsm_bit_pattern_detection fsm_bit_pattern_detection_sva sva_i();

module fsm_bit_pattern_detection_sva;
  // Mirror DUT encodings
  localparam logic [1:0] S0=2'b00, S1=2'b01, S2=2'b10, S3=2'b11;
  localparam logic [7:0] P = 8'b10110101;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // Make $past() safe
  bit past_valid;
  always_ff @(posedge clk) past_valid <= !reset;

  // Reset behavior
  assert property (@(posedge clk) reset |=> state==S0 && shift_reg==8'h00 && pulse==1'b0);

  // Basic sanity
  assert property (past_valid |-> !$isunknown(state) && state inside {S0,S1,S2,S3});
  assert property (past_valid |-> !$isunknown(pulse));

  // S0 transitions
  assert property (past_valid && $past(state)==S0 && $past(shift_reg)==P |-> state==S3 && pulse);
  assert property (past_valid && $past(state)==S0 && $past(shift_reg)!=P && $past(shift_reg[7])==1'b1 |-> state==S1);
  assert property (past_valid && $past(state)==S0 && $past(shift_reg[7])==1'b0 |-> state==S0);

  // S1 transitions
  assert property (past_valid && $past(state)==S1 && $past(shift_reg[7:6])==2'b10 |-> state==S2);
  assert property (past_valid && $past(state)==S1 && $past(shift_reg[7])==1'b0 |-> state==S0);
  assert property (past_valid && $past(state)==S1 && $past(shift_reg[7:6])!=2'b10 && $past(shift_reg[7])==1'b1 |-> state==S1);

  // S2 transitions
  assert property (past_valid && $past(state)==S2 && $past(shift_reg[7:5])==3'b101 |-> state==S3 && pulse);
  assert property (past_valid && $past(state)==S2 && $past(shift_reg[7:6])!=2'b10 |-> state==S0);
  assert property (past_valid && $past(state)==S2 && $past(shift_reg[7:6])==2'b10 && $past(shift_reg[7:5])!=3'b101 |-> state==S2);

  // S3 transitions
  assert property (past_valid && $past(state)==S3 && $past(shift_reg)==P |-> state==S3);
  assert property (past_valid && $past(state)==S3 && $past(shift_reg)!=P |-> state==S0);

  // Pulse semantics (quality checks)
  assert property (state==S3 |-> pulse);          // must be high in S3
  assert property (pulse |-> state==S3);          // never high outside S3
  assert property ($rose(pulse) |=> !pulse);      // single-cycle pulse

  // As-coded shift_reg update effect (exposes truncation of concat)
  assert property (past_valid |-> shift_reg == $past(data));

  // Coverage
  cover property ($rose(pulse));
  cover property (state==S0 ##1 state==S3);                         // direct detect
  cover property (state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);
endmodule