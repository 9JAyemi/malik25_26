// SVA for inverted_5input_OR_gate
// Bindable, concise, and complete for combinational correctness and coverage

module inverted_5input_OR_gate_sva (
  input logic p1, p2, p3, p4, p5,
  input logic y
);
  // Pack inputs for compact expressions
  logic [4:0] p = {p5,p4,p3,p2,p1};

  // Functional equivalence (allow delta for NBA update)
  ap_func: assert property (@(*) !$isunknown(p) |-> ##0 (y == ~(|p)));

  // If inputs are known, output must be known after settle
  ap_known: assert property (@(*) !$isunknown(p) |-> ##0 !$isunknown(y));

  // Basic coverage: both output values reachable
  cp_y1: cover property (@(*) (!|p) ##0 (y == 1'b1));
  cp_y0: cover property (@(*) (|p)  ##0 (y == 1'b0));

  // Full input-space coverage with expected output
  generate
    genvar k;
    for (k = 0; k < 32; k++) begin : GEN_ALL_COMBOS
      cp_all: cover property (@(*) (p == k[4:0]) ##0 (y == ~(|k[4:0])));
    end
  endgenerate
endmodule

// Bind into the DUT
bind inverted_5input_OR_gate inverted_5input_OR_gate_sva sva_i (
  .p1(p1), .p2(p2), .p3(p3), .p4(p4), .p5(p5), .y(y)
);