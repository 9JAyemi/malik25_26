// SVA for top_module and sub-block behaviors
// Bind this checker to the DUT
bind top_module top_module_sva i_top_module_sva (.*);

module top_module_sva (
  input clk,
  input reset,
  input data,
  input q,
  input [2:0] shift_reg,
  input [2:0] complement
);
  default clocking cb @(posedge clk); endclocking

  // Track when $past is valid after (re)setting
  logic past_v;
  always @(posedge clk) if (reset) past_v <= 1'b0; else past_v <= 1'b1;

  // Synchronous reset values (same-cycle)
  assert property (@(posedge clk) reset |-> (shift_reg == 3'b000 && q == 1'b0));

  // Shift-register next-state function
  assert property (disable iff (reset)
    past_v && !$past(reset) |-> shift_reg == { $past(shift_reg[1:0]), $past(data) }
  );

  // Functional module: out is bitwise complement of in1
  assert property (complement == ~shift_reg);

  // End-to-end: q equals prior cycle MSB of complement(~shift_reg[2])
  assert property (disable iff (reset)
    past_v && !$past(reset) |-> q == $past(~shift_reg[2])
  );

  // No X/Z on key state once out of reset
  assert property (disable iff (reset)
    !$isunknown({shift_reg, complement, q})
  );

  // Coverage
  cover property (@(posedge clk) reset ##1 !reset);
  cover property (disable iff (reset)
    (shift_reg==3'b000) ##1 (shift_reg==3'b001) ##1 (shift_reg==3'b011) ##1 (shift_reg==3'b111)
  );
  cover property (disable iff (reset) $rose(q));
  cover property (disable iff (reset) $fell(q));
endmodule