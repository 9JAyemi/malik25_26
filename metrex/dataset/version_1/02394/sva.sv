// SVA checker for shift_register
module shift_register_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  d,
  input logic        enable,
  input logic [3:0]  q,
  input logic [3:0]  q_reg1,
  input logic [3:0]  q_reg2,
  input logic [3:0]  q_reg3,
  input logic [3:0]  q_reg4
);

  default clocking cb @(posedge clk); endclocking

  // Track $past validity
  logic past_valid;
  always @(cb) begin
    if (!reset) past_valid <= 1'b0;
    else        past_valid <= 1'b1;
  end

  // Async reset drives/holds zeros
  ap_reset_zeros: assert property ( !reset |-> (q==4'b0 && q_reg1==4'b0 && q_reg2==4'b0 && q_reg3==4'b0 && q_reg4==4'b0) );

  // Output mirrors q_reg4
  ap_q_matches:   assert property ( q == q_reg4 );

  // Hold behavior when disabled
  ap_hold:  assert property ( disable iff (!reset)
                              past_valid && !enable |=> (q_reg1==$past(q_reg1) && q_reg2==$past(q_reg2)
                                                      &&  q_reg3==$past(q_reg3) && q_reg4==$past(q_reg4)
                                                      &&  q==$past(q)) );

  // Shift behavior when enabled
  ap_shift: assert property ( disable iff (!reset)
                              past_valid && enable |=> (q_reg1==$past(d[0])   && q_reg2==$past(q_reg1)
                                                    &&  q_reg3==$past(q_reg2) && q_reg4==$past(q_reg3)
                                                    &&  q==$past(q_reg3)) );

  // Invariant: upper bits remain zero (width-mismatch sentinel)
  ap_upper_zero: assert property ( (q_reg1[3:1]==3'b0) && (q_reg2[3:1]==3'b0)
                                && (q_reg3[3:1]==3'b0) && (q_reg4[3:1]==3'b0)
                                && (q[3:1]==3'b0) );

  // Coverage: observe reset activity
  cp_reset:  cover property ( $fell(reset) );

  // Coverage: a '1' on d[0] shifts through to q in 4 enabled cycles
  sequence en4; enable ##1 enable ##1 enable ##1 enable; endsequence
  cp_shift1: cover property ( disable iff (!reset)
                              (enable && d[0]) ##1 enable ##1 enable ##1 enable |-> (q == 4'b0001) );

  // Coverage: hold for 3 cycles when disabled
  cp_hold3:  cover property ( disable iff (!reset) !enable[*3] );

endmodule

// Bind to DUT
bind shift_register shift_register_sva u_shift_register_sva (
  .clk    (clk),
  .reset  (reset),
  .d      (d),
  .enable (enable),
  .q      (q),
  .q_reg1 (q_reg1),
  .q_reg2 (q_reg2),
  .q_reg3 (q_reg3),
  .q_reg4 (q_reg4)
);