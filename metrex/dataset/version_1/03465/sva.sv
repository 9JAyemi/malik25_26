// SVA for DTR. Bind this module to the DUT.
// Focus: correct counter stepping, per-count output updates, stability when no write, and legal transitions only.

module DTR_sva (
  input STARTPULSE,
  input DTROUT7, DTROUT6, DTROUT5, DTROUT4, DTROUT3, DTROUT2, DTROUT1, DTROUT0,
  input [2:0] counter
);
  default clocking cb @(posedge STARTPULSE); endclocking

  // past_valid to safely use $past()
  bit past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge STARTPULSE) past_valid <= 1'b1;
  default disable iff (!past_valid);

  wire [7:0] dout = {DTROUT7,DTROUT6,DTROUT5,DTROUT4,DTROUT3,DTROUT2,DTROUT1,DTROUT0};

  // Counter must increment modulo-8 each STARTPULSE
  a_cnt_inc: assert property (counter == $past(counter) + 3'd1);

  // Per-counter behaviors (effects visible next clock sample)
  a_case0:   assert property ($past(counter)==3'd0 |-> dout[4:0] == 5'b11111 && $stable({DTROUT7,DTROUT6,DTROUT5}));
  a_case1:   assert property ($past(counter)==3'd1 |-> DTROUT5 && $stable({DTROUT7,DTROUT6,DTROUT4,DTROUT3,DTROUT2,DTROUT1,DTROUT0}));
  a_case2:   assert property ($past(counter)==3'd2 |-> DTROUT6 && $stable({DTROUT7,DTROUT5,DTROUT4,DTROUT3,DTROUT2,DTROUT1,DTROUT0}));
  a_case3:   assert property ($past(counter)==3'd3 |-> dout == 8'b1000_0000);
  a_case4_7: assert property ($past(counter) inside {[3'd4:3'd7]} |-> $stable(dout));

  // Only-when constraints on transitions
  a_rise_4_0_only_on0: assert property ( ($rose(DTROUT4)||$rose(DTROUT3)||$rose(DTROUT2)||$rose(DTROUT1)||$rose(DTROUT0)) |-> $past(counter)==3'd0 );
  a_rise_5_only_on1:   assert property ( $rose(DTROUT5) |-> $past(counter)==3'd1 );
  a_rise_6_only_on2:   assert property ( $rose(DTROUT6) |-> $past(counter)==3'd2 );
  a_rise_7_only_on3:   assert property ( $rose(DTROUT7) |-> $past(counter)==3'd3 );

  // Any falling edge on bits [6:0] only occurs on clear phase (counter==3)
  a_fall_6_0_only_on3: assert property ( ($fell(DTROUT6)||$fell(DTROUT5)||$fell(DTROUT4)||$fell(DTROUT3)||$fell(DTROUT2)||$fell(DTROUT1)||$fell(DTROUT0)) |-> $past(counter)==3'd3 );

  // DTROUT7 never falls (final assignment in counter==3 sets it to 1)
  a_no_fall_7: assert property ( !$fell(DTROUT7) );

  // Minimal functional coverage
  c_seq_0_1_2_3: cover property (counter==3'd0 ##1 counter==3'd1 ##1 counter==3'd2 ##1 counter==3'd3);
  c_set_low5:    cover property ($past(counter)==3'd0 |-> dout[4:0]==5'b11111);
  c_set_d5:      cover property ($past(counter)==3'd1 |-> DTROUT5);
  c_set_d6:      cover property ($past(counter)==3'd2 |-> DTROUT6);
  c_clear_set7:  cover property ($past(counter)==3'd3 |-> dout==8'b1000_0000);

endmodule

bind DTR DTR_sva sva_DTR (.*);