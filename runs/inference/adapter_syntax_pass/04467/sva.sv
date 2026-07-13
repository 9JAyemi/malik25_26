module RegisterAdd__parameterized5_sva
  #(parameter N = 23)
  (
    input logic [N-1:0] Q,
    input logic [0:0]   E,
    input logic [N-1:0] D,
    input logic         CLK,
    input logic [0:0]   AR
  );

  // Active-low reset clears Q to zero.
  check_reset_clears_q: assert property (
    @(posedge CLK) !AR |-> (Q == {N{1'b0}})
  );

  // When enabled, Q updates to D plus the previous Q.
  check_enabled_update: assert property (
    @(posedge CLK) disable iff (!AR) E |-> (Q == ($past(Q) + D))
  );

  // When disabled, Q holds its previous value.
  check_hold_when_disabled: assert property (
    @(posedge CLK) disable iff (!AR) !E |-> (Q == $past(Q))
  );

  // The first cycle after reset release still sees Q at zero.
  check_post_reset_zero: assert property (
    @(posedge CLK) $rose(AR) |-> (Q == {N{1'b0}})
  );

  // With E high and D equal to zero, Q clears on the next cycle.
  check_clear_when_enabled_and_zero_data: assert property (
    @(posedge CLK) disable iff (!AR) (E && (D == {N{1'b0}})) |-> (Q == {N{1'b0}})
  );

  // With E high and D equal to one, Q increments by one.
  check_increment_when_enabled_and_one_data: assert property (
    @(posedge CLK) disable iff (!AR) (E && (D == {{(N-1){1'b0}}, 1'b1})) |-> (Q == ($past(Q) + 1))
  );

  // With E high and D equal to all ones, Q becomes all ones.
  check_all_ones_when_enabled_and_all_ones_data: assert property (
    @(posedge CLK) disable iff (!AR) (E && (D == {N{1'b1}})) |-> (Q == {N{1'b1}})
  );

endmodule