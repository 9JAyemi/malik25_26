// SVA for mux_2_1_syncreset
// Concise, high-quality checks with essential coverage

module mux_2_1_syncreset_sva (
  input  logic        clk,
  input  logic        rst,
  input  logic        sel,
  input  logic [31:0] in1,
  input  logic [31:0] in2,
  input  logic [31:0] out
);

  default clocking cb @(posedge clk); endclocking

  // Core functional check (includes reset priority). Use case equality to honor X-prop.
  ap_func: assert property (@cb 1'b1 |-> ##0 (out === (rst ? 32'h0 : (sel ? in1 : in2))));

  // Reset produces zero each cycle it is asserted
  ap_rst_zero: assert property (@cb rst |-> ##0 (out === 32'h0000_0000));

  // Control must be known when used (prevents accidental X-driven select while not in reset)
  ap_sel_known_when_active: assert property (@cb !rst |-> !$isunknown(sel));

  // No spurious output changes when selected input and sel are stable across cycles
  ap_no_spurious_change: assert property (@cb !rst && $stable(sel) && $stable(sel ? in1 : in2) |=> $stable(out));

  // Coverage
  cp_reset_pulse: cover property (@cb rst ##1 !rst);
  cp_take_in1:    cover property (@cb !rst && sel  |-> ##0 (out === in1));
  cp_take_in2:    cover property (@cb !rst && !sel |-> ##0 (out === in2));
  cp_sel_01:      cover property (@cb !rst && !sel ##1 !rst && sel);
  cp_sel_10:      cover property (@cb !rst && sel  ##1 !rst && !sel);

endmodule

// Bind into DUT
bind mux_2_1_syncreset mux_2_1_syncreset_sva sva_i(.*);