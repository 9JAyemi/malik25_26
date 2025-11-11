// SVA checker for addition_module
// Concise, full functional check + key coverage. Bind into DUT.

module addition_module_sva
  (
    input logic [1:0] i,
    input logic [1:0] a,
    input logic [1:0] o
  );

  // Create a sampling event whenever inputs change
  logic sv_ev;
  initial sv_ev = 1'b0;
  always @(i or a) sv_ev <= ~sv_ev;

  default clocking cb @(posedge sv_ev); endclocking

  // Functional correctness (sample after design updates via ##0)
  ap_sum: assert property (
    disable iff ($isunknown({i,a}))
    1'b1 |-> ##0 (o == 2'(i + a))
  );

  // If inputs are known, output must be known (no X/Z leakage)
  ap_known_out: assert property (
    (!$isunknown({i,a})) |-> ##0 (!$isunknown(o))
  );

  // Coverage: hit every input combination (16) and every output value (4)
  genvar k;
  generate
    for (k = 0; k < 16; k++) begin : cov_inputs
      cp_in: cover property (##0 ({i,a} == 4'(k)));
    end
    for (k = 0; k < 4; k++) begin : cov_outputs
      cp_out: cover property (##0 (o == 2'(k)));
    end
  endgenerate

  // Coverage: observe overflow/wrap (sum >= 4)
  cp_overflow: cover property (##0 ((i + a) >= 4));

endmodule

// Bind into the DUT
bind addition_module addition_module_sva u_addition_module_sva (.i(i), .a(a), .o(o));