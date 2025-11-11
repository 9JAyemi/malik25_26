// SVA for async_reset_release
// Bind example:
// bind async_reset_release async_reset_release_sva sva (.*);

module async_reset_release_sva (input logic clk, rst, in, out);

  default clocking cb @(posedge clk); endclocking

  // Single-step next-state equivalence (concise, canonical)
  // Next out must equal (rst ? 0 : in) sampled in the previous cycle
  a_next_state: assert property (1'b1 |=> out == ($past(rst) ? 1'b0 : $past(in)));

  // Reset behavior clarity
  a_rst_clears_next: assert property (rst |=> out == 1'b0);
  a_rst_holds_zero:  assert property (rst && $past(rst) |-> out == 1'b0);

  // Data capture when not in reset for 2+ consecutive cycles
  a_pipe: assert property (!rst && !$past(rst) |-> out == $past(in));

  // After reset release, first captured value is in at release cycle
  a_capture_after_release: assert property ($fell(rst) |=> out == $past(in));

  // Output must never be X/Z
  a_no_x_out: assert property (!$isunknown(out));

  // Minimal functional coverage
  c_rst_assert:      cover property ($rose(rst));
  c_rst_deassert:    cover property ($fell(rst));
  c_rst_pulse:       cover property ($rose(rst) ##1 rst ##1 $fell(rst));
  c_cap_0_to_1:      cover property (!rst && !$past(rst) && $past(in)==0 && in==1 ##1 out==1);
  c_cap_1_to_0:      cover property (!rst && !$past(rst) && $past(in)==1 && in==0 ##1 out==0);

endmodule