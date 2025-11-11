// SVA checker for mux_2to1
module mux_2to1_sva (
  input logic in0,
  input logic in1,
  input logic sel,
  input logic out
);

  // Sample on any relevant input change
  default clocking cb @(in0 or in1 or sel); endclocking

  // Functional correctness for known select
  a_sel0: assert property (sel === 1'b0 |-> out === in0);
  a_sel1: assert property (sel === 1'b1 |-> out === in1);

  // Equal inputs collapse regardless of select (incl. X/Z)
  a_equal_inputs: assert property ((in0 === in1) |-> (out === in0));

  // X-propagation when select is X/Z and inputs differ
  a_selx_diff: assert property ((sel !== 1'b0 && sel !== 1'b1 && (in0 !== in1)) |-> $isunknown(out));

  // Output only changes if a driver (in0/in1/sel) changed since last time
  a_no_spurious_out: assert property (@(out) ($changed(in0) || $changed(in1) || $changed(sel)));

  // Coverage
  cover_sel0:      cover property (sel === 1'b0 && out === in0);
  cover_sel1:      cover property (sel === 1'b1 && out === in1);
  cover_rise_sel:  cover property ($rose(sel) && out === in1);
  cover_fall_sel:  cover property ($fell(sel) && out === in0);
  cover_selx_eq:   cover property ((sel !== 1'b0 && sel !== 1'b1) && (in0 === in1) && (out === in0));
  cover_selx_diff: cover property ((sel !== 1'b0 && sel !== 1'b1) && (in0 !== in1) && $isunknown(out));

endmodule

// Bind into DUT
bind mux_2to1 mux_2to1_sva u_mux_2to1_sva(.in0(in0), .in1(in1), .sel(sel), .out(out));