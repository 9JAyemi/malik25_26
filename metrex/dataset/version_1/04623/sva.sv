// SVA for four_bit_register
module four_bit_register_sva (
  input logic       CLK,
  input logic       RST,     // active-low async
  input logic [3:0] D,
  input logic [3:0] Q
);

  // Guard for $past at time 0 / after reset
  logic past_valid;
  always @(posedge CLK or negedge RST) begin
    if (!RST) past_valid <= 1'b0;
    else      past_valid <= 1'b1;
  end

  // Async reset takes effect immediately (after NBA in same timestep)
  ap_async_reset_immediate: assert property (@(negedge RST) ##0 (Q == 4'b0));

  // While in reset, Q is 0 and stable across clock edges
  ap_reset_holds_zero:      assert property (@(posedge CLK) !RST |-> (Q == 4'b0));
  ap_reset_stable_on_clk:   assert property (@(posedge CLK) !RST |-> $stable(Q));

  // RST must be known at clock edges
  ap_rst_known:             assert property (@(posedge CLK) !$isunknown(RST));

  // First clock after reset release: Q still 0 at the sample point
  ap_first_clk_after_rel:   assert property (@(posedge CLK) past_valid && RST && !$past(RST) |-> (Q == 4'b0));

  // Normal operation: Q captures D with 1-cycle latency when not coming out of reset
  ap_sync_capture:          assert property (@(posedge CLK) past_valid && RST && $past(RST) |-> (Q == $past(D)));

  // Optional: if captured D was known, Q becomes known next cycle
  ap_known_propagation:     assert property (@(posedge CLK) past_valid && RST && $past(RST) && !$isunknown($past(D)) |=> !$isunknown(Q));

  // Coverage
  cv_reset_assert:          cover  property (@(negedge RST) 1);
  cv_reset_release:         cover  property (@(posedge CLK) past_valid && RST && !$past(RST));
  cv_data_cap_change:       cover  property (@(posedge CLK) past_valid && RST && $past(RST) && (D != $past(D)) |=> (Q == $past(D)));
  cv_q_toggle:              cover  property (@(posedge CLK) past_valid && RST && $past(RST) && (Q != $past(Q)));

endmodule

bind four_bit_register four_bit_register_sva sva (.CLK(CLK), .RST(RST), .D(D), .Q(Q));