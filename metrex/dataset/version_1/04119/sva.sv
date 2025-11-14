// SVA for mux4 — concise, high-quality checks and coverage.
// Bind into mux4 and provide a sampling clock from TB/formal.
//
// Example bind (replace tb_clk as appropriate):
//   bind mux4 mux4_sva u_mux4_sva(.clk(tb_clk), .rst_n(1'b1));

module mux4_sva (
  input logic clk,
  input logic rst_n,

  // These ports are auto-connected by bind to the mux4 instance
  input logic [3:0] in0,
  input logic [3:0] in1,
  input logic [3:0] in2,
  input logic [3:0] in3,
  input logic       s0,
  input logic       s1,
  input logic [3:0] out
);
  default clocking cb @(posedge clk); endclocking

  // Deterministic selects (avoid X/Z on control)
  a_sel_2state: assert property (disable iff (!rst_n)
    !$isunknown({s1,s0})
  );

  // Core functional equivalence (truth table) — single concise check
  a_truth: assert property (disable iff (!rst_n)
    out == (s1 ? (s0 ? in3 : in1)
               : (s0 ? in2 : in0))
  );

  // Internal path checks (bound into mux4 scope; w1/w2 are visible here)
  a_w1_sel: assert property (disable iff (!rst_n)
    w1 == (s0 ? in2 : in0)
  );
  a_w2_sel: assert property (disable iff (!rst_n)
    w2 == (s0 ? in3 : in1)
  );

  // No spurious X on out when all inputs/controls are known
  a_no_x_when_known: assert property (disable iff (!rst_n)
    (!$isunknown({s1,s0,in0,in1,in2,in3})) |-> !$isunknown(out)
  );

  // Coverage: hit all select combinations with correct mapping
  c_00: cover property (disable iff (!rst_n)
    {s1,s0}==2'b00 && out==in0
  );
  c_01: cover property (disable iff (!rst_n)
    {s1,s0}==2'b01 && out==in2
  );
  c_10: cover property (disable iff (!rst_n)
    {s1,s0}==2'b10 && out==in1
  );
  c_11: cover property (disable iff (!rst_n)
    {s1,s0}==2'b11 && out==in3
  );

  // Coverage: exercise select changes
  c_sel_toggle: cover property (disable iff (!rst_n) $changed({s1,s0}));

endmodule