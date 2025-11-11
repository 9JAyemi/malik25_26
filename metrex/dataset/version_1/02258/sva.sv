// SVA checker for binary_counter
module binary_counter_sva (
  input        clk,
  input        reset,
  input  [1:0] state,
  input  [1:0] next_state,
  input  [3:0] q
);

  // Mirror DUT encodings
  localparam [1:0] S0 = 2'b00,
                   S1 = 2'b01,
                   S2 = 2'b10,
                   S3 = 2'b11;

  default clocking cb @(posedge clk); endclocking
  default disable iff (reset);

  // --------------------
  // Basic sanity / X checks
  // --------------------
  ap_no_x: assert property (@(posedge clk or posedge reset) !$isunknown({state,next_state,q}));

  ap_state_in_range: assert property (@(posedge clk or posedge reset)
                                      state inside {S0,S1,S2,S3});

  // --------------------
  // Asynchronous reset behavior
  // --------------------
  ap_async_reset_immediate: assert property (@(posedge reset) state==S0 && q==4'b0000);

  ap_reset_hold: assert property (@(posedge clk) reset |-> (state==S0 && q==4'b0000));

  // After reset deasserts, first active clock advances to S1
  ap_reset_release_advances: assert property (@(posedge clk) $past(reset) && !reset |-> state==S1);

  // --------------------
  // Next-state function correctness (combinational)
  // --------------------
  ap_next_state_func: assert property (@(posedge clk or posedge reset)
                                       next_state == (state==S0 ? S1 :
                                                      state==S1 ? S2 :
                                                      state==S2 ? S3 : S0));

  // --------------------
  // Registered state transitions
  // --------------------
  ap_s0_s1: assert property (state==S0 |=> state==S1);
  ap_s1_s2: assert property (state==S1 |=> state==S2);
  ap_s2_s3: assert property (state==S2 |=> state==S3);
  ap_s3_s0: assert property (state==S3 |=> state==S0);

  // --------------------
  // Output decode mapping
  // --------------------
  ap_q_mapping: assert property (@(posedge clk or posedge reset)
                                 (state==S0 && q==4'b0000) ||
                                 (state==S1 && q==4'b0001) ||
                                 (state==S2 && q==4'b0010) ||
                                 (state==S3 && q==4'b0011));

  // Optional: q transition consistency (derivable from above, but explicit)
  ap_q_sequence:
    assert property ( (q==4'b0000) |=> (q==4'b0001) |=> (q==4'b0010) |=> (q==4'b0011) |=> (q==4'b0000) );

  // --------------------
  // Coverage
  // --------------------
  cv_each_state_S0: cover property (state==S0);
  cv_each_state_S1: cover property (state==S1);
  cv_each_state_S2: cover property (state==S2);
  cv_each_state_S3: cover property (state==S3);

  cv_full_cycle: cover property (state==S0 ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);

  cv_reset_then_cycle:
    cover property (@(posedge clk) $past(reset) && !reset ##1 state==S1 ##1 state==S2 ##1 state==S3 ##1 state==S0);

endmodule

// Bind the checker into the DUT
bind binary_counter binary_counter_sva u_binary_counter_sva (
  .clk       (clk),
  .reset     (reset),
  .state     (state),
  .next_state(next_state),
  .q         (q)
);