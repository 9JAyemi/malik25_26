// SVA checker for assert_even_parity_assert
module assert_even_parity_assert_sva #(parameter int width=1)
(
  input logic                   clk,
  input logic                   reset_n,
  input logic [width-1:0]       test_expr,
  input logic                   xzcheck_enable,
  input logic                   parity_result,
  input logic [width-1:0]       data,      // internal
  input logic                   parity     // internal
);

  // Reset values must hold while reset is asserted
  ap_reset_vals_hold: assert property (@(posedge clk)
    !reset_n |-> (parity==1'b1 && parity_result==1'b0));

  // Registered data capture
  ap_data_cap: assert property (@(posedge clk)
    disable iff (!reset_n)
    $past(reset_n) |-> (data == $past(test_expr)));

  // Parity updates from previous-cycle test_expr
  ap_parity_update: assert property (@(posedge clk)
    disable iff (!reset_n)
    $past(reset_n) |-> (parity == ^$past(test_expr)));

  // Parity_result is complement of previous-cycle parity
  ap_parity_result_from_parity: assert property (@(posedge clk)
    disable iff (!reset_n)
    $past(reset_n) |-> (parity_result == ~$past(parity)));

  // Two-cycle relation: parity_result vs test_expr
  ap_parity_result_vs_testexpr: assert property (@(posedge clk)
    disable iff (!reset_n)
    $past(reset_n,2) |-> (parity_result == ~(^$past(test_expr,2))));

  // Same-cycle consistency when X/Z checks enabled
  ap_consistency_when_known: assert property (@(posedge clk)
    disable iff (!reset_n)
    (xzcheck_enable && $past(reset_n)) |-> (parity == ^data));

  // X/Z hygiene when enabled
  ap_no_xz_in: assert property (@(posedge clk)
    disable iff (!reset_n)
    xzcheck_enable |-> !$isunknown(test_expr));
  ap_no_xz_out: assert property (@(posedge clk)
    disable iff (!reset_n)
    xzcheck_enable |-> (!$isunknown(parity) && !$isunknown(parity_result)));

  // Minimal coverage
  cp_parity_odd:      cover property (@(posedge clk) disable iff (!reset_n) parity==1'b1);
  cp_parity_evenflag: cover property (@(posedge clk) disable iff (!reset_n) parity_result==1'b1);
  cp_pr_toggle:       cover property (@(posedge clk) disable iff (!reset_n) $changed(parity_result));
  cp_xz_path_used:    cover property (@(posedge clk) disable iff (!reset_n) xzcheck_enable && !$isunknown(test_expr));

endmodule

// Bind into DUT (accesses internal regs data/parity)
bind assert_even_parity_assert
  assert_even_parity_assert_sva #(.width(width)) i_assert_even_parity_assert_sva (
    .clk(clk),
    .reset_n(reset_n),
    .test_expr(test_expr),
    .xzcheck_enable(xzcheck_enable),
    .parity_result(parity_result),
    .data(data),
    .parity(parity)
  );