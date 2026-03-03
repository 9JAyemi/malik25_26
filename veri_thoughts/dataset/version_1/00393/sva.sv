// SVA for counter_with_reset
module counter_with_reset_sva (
  input logic        clk,
  input logic        reset,
  input logic [3:0]  count_out
);
  default clocking cb @(posedge clk); endclocking

  // Reset behavior
  assert property (reset |-> count_out == 4'h0);

  // First non-reset cycle after reset increments from 0 -> 1
  assert property (!reset && $past(reset) |-> count_out == 4'h1);

  // Increment on consecutive non-reset cycles
  assert property (!reset && !$past(reset) && !$isunknown($past(count_out)) && ($past(count_out) != 4'hF)
                   |-> count_out == $past(count_out)+1);

  // Wrap from F->0 on consecutive non-reset cycles
  assert property (!reset && !$past(reset) && ($past(count_out) == 4'hF)
                   |-> count_out == 4'h0);

  // No X on output when not in reset
  assert property (!reset |-> !$isunknown(count_out));

  // Coverage: see all values and a wrap
  genvar v;
  generate
    for (v=0; v<16; v++) begin : C_VALS
      cover property (!reset && count_out == v[3:0]);
    end
  endgenerate
  cover property (!$past(reset) && !reset && $past(count_out)==4'hF && count_out==4'h0);
  cover property ($rose(reset));
endmodule

bind counter_with_reset counter_with_reset_sva u_counter_with_reset_sva (
  .clk(clk), .reset(reset), .count_out(count_out)
);

// SVA for barrel_shifter bound at top (uses top clk and internal net)
module top_module_sva (
  input logic        clk,
  input logic        reset,
  input logic [15:0] data_in,
  input logic [3:0]  shift_amt,
  input logic [15:0] shifted_data
);
  default clocking cb @(posedge clk); endclocking

  // Functional equivalence to logical left shift with zero fill
  assert property ((!$isunknown(data_in) && !$isunknown(shift_amt))
                   |-> shifted_data == (data_in << shift_amt));

  // Output known when inputs known
  assert property ((!$isunknown(data_in) && !$isunknown(shift_amt))
                   |-> !$isunknown(shifted_data));

  // Coverage: exercise all shift amounts
  genvar s;
  generate
    for (s=0; s<16; s++) begin : C_SHAMT
      cover property (shift_amt == s[3:0]);
    end
  endgenerate
  cover property (shift_amt==4'd0);
  cover property (shift_amt==4'd15);
endmodule

bind top_module top_module_sva u_top_module_sva (
  .clk(clk), .reset(reset),
  .data_in(data_in), .shift_amt(shift_amt), .shifted_data(shifted_data)
)