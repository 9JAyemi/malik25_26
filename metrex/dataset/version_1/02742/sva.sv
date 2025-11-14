// SVA checker bound into the DUT
module digit_state_machine_sva;
  // Use DUT scope signals via portless bind
  default clocking cb @(posedge clk); endclocking

  // Asynchronous reset behavior (sampled on clk)
  ap_reset_state: assert property (@cb (!reset_n |-> state == S0));

  // State must be known out of reset
  ap_state_known: assert property (@cb disable iff (!reset_n) !$isunknown(state));

  // Sequential state progression
  ap_s0_s1: assert property (@cb disable iff (!reset_n) (state==S0 |=> state==S1));
  ap_s1_s2: assert property (@cb disable iff (!reset_n) (state==S1 |=> state==S2));
  ap_s2_s3: assert property (@cb disable iff (!reset_n) (state==S2 |=> state==S3));
  ap_s3_s0: assert property (@cb disable iff (!reset_n) (state==S3 |=> state==S0));

  // Combinational next-state mapping
  ap_ns_s0: assert property (@cb disable iff (!reset_n) (state==S0 |-> state_n==S1));
  ap_ns_s1: assert property (@cb disable iff (!reset_n) (state==S1 |-> state_n==S2));
  ap_ns_s2: assert property (@cb disable iff (!reset_n) (state==S2 |-> state_n==S3));
  ap_ns_s3: assert property (@cb disable iff (!reset_n) (state==S3 |-> state_n==S0));

  // Flop loads previous cycle's next-state
  ap_state_from_ns: assert property (@cb disable iff (!reset_n) state == $past(state_n));

  // Output decode per state (use case-equality for X-tolerant data propagation)
  ap_out_s0: assert property (@cb disable iff (!reset_n)
                              (state==S0 |-> decimal_point==1'b1 && digit_select==3'b000 && (data === units)));
  ap_out_s1: assert property (@cb disable iff (!reset_n)
                              (state==S1 |-> decimal_point==1'b1 && digit_select==3'b001 && (data === tens)));
  ap_out_s2: assert property (@cb disable iff (!reset_n)
                              (state==S2 |-> decimal_point==1'b1 && digit_select==3'b011 && (data === hundreds)));
  ap_out_s3: assert property (@cb disable iff (!reset_n)
                              (state==S3 |-> decimal_point==1'b0 && digit_select==3'b100 && (data === thousands)));

  // Decimal point consistency with state
  ap_dp_consistent: assert property (@cb disable iff (!reset_n) (decimal_point == (state != S3)));

  // Digit-select must follow the 4-phase sequence
  ap_ds_seq: assert property (@cb disable iff (!reset_n)
                              (digit_select==3'b000 |=> digit_select==3'b001 |=> digit_select==3'b011
                               |=> digit_select==3'b100 |=> digit_select==3'b000));

  // Control outputs known
  ap_ctrl_known: assert property (@cb disable iff (!reset_n) !$isunknown({decimal_point,digit_select}));

  // Coverage
  cp_full_cycle: cover property (@cb disable iff (!reset_n)
                                 (state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0));
  cp_out_cycle:  cover property (@cb disable iff (!reset_n)
                                 (digit_select==3'b000 ##1 3'b001 ##1 3'b011 ##1 3'b100 ##1 3'b000));
  cp_s0: cover property (@cb disable iff (!reset_n) (state==S0 && decimal_point && digit_select==3'b000 && (data === units)));
  cp_s1: cover property (@cb disable iff (!reset_n) (state==S1 && decimal_point && digit_select==3'b001 && (data === tens)));
  cp_s2: cover property (@cb disable iff (!reset_n) (state==S2 && decimal_point && digit_select==3'b011 && (data === hundreds)));
  cp_s3: cover property (@cb disable iff (!reset_n) (state==S3 && !decimal_point && digit_select==3'b100 && (data === thousands)));
endmodule

bind digit_state_machine digit_state_machine_sva sva_i;