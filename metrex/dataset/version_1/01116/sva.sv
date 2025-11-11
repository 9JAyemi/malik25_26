// SVA for shift_register
// Bind this file to the DUT; focuses on correctness, width-sanity, X-checking, and concise coverage.

module shift_register_sva (
  input clk,
  input rst,
  input [3:0] shift_in,
  input [3:0] shift_out
);

  default clocking cb @(posedge clk); endclocking

  // Static width sanity: RHS concat must match LHS width (will FAIL for given RTL: 7 vs 4)
  initial begin
    assert ($bits(shift_out) == $bits({shift_out[2:0], shift_in}))
      else $error("shift_register width mismatch: LHS=%0d, RHS concat=%0d",
                  $bits(shift_out), $bits({shift_out[2:0], shift_in}));
  end

  // Reset must synchronously clear output to zero whenever rst==1 at the clock edge
  a_reset_clears: assert property (rst |-> (shift_out == 4'b0000));

  // No X/Zs during active operation
  a_no_x_in_when_active:  assert property (disable iff (rst) !$isunknown(shift_in));
  a_no_x_out_when_active: assert property (disable iff (rst) !$isunknown(shift_out));

  // Functional next-state check:
  // If shift_in were 1-bit: true shift-left with serial-in
  // Else (as written: 4-bit), behavior degenerates to parallel load due to truncation.
  generate
    if ($bits(shift_in) == 1) begin : G_INTENDED
      a_shift: assert property (disable iff (rst)
                                shift_out == { $past(shift_out[2:0]), shift_in });
      // Simple functional coverage: observe a walking-1 pattern
      c_walk1: cover property (disable iff (rst)
                               (shift_in==1'b1) ##1 (shift_in==1'b0)[*3] ##1
                               (shift_out==4'b0001 || shift_out==4'b0010 ||
                                shift_out==4'b0100 || shift_out==4'b1000));
    end else begin : G_TRUNC
      // RTL-as-written check: output equals shift_in each active cycle
      a_loads_instead_of_shift: assert property (disable iff (rst) (shift_out == shift_in));
    end
  endgenerate

  // Compact coverage
  c_reset_seen:     cover property (rst);
  c_deassert_seen:  cover property ($fell(rst));
  c_out_changes:    cover property (disable iff (rst) shift_out != $past(shift_out));

endmodule

bind shift_register shift_register_sva u_shift_register_sva (.*);