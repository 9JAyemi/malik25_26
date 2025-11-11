// SVA checker for Vector; combinational, clockless using event-based sampling with ##0 settle
module Vector_sva #(parameter int WIDTH = 2)
(
  input logic [WIDTH-1:0] a,
  input logic [WIDTH-1:0] b,
  input logic [WIDTH-1:0] c
);

  // Functional equivalence: c must be bitwise AND of a and b
  property p_and_correct;
    @(a or b) 1'b1 |-> ##0 (c === (a & b));
  endproperty
  assert property (p_and_correct);

  // If inputs are known, output must be known (no X/Z leakage)
  property p_known_inputs_implies_known_output;
    @(a or b) (!$isunknown({a,b})) |-> ##0 (!$isunknown(c));
  endproperty
  assert property (p_known_inputs_implies_known_output);

  // Full input-space coverage with correctness
  genvar I, J;
  generate
    for (I = 0; I < (1<<WIDTH); I++) begin : GEN_A_VAL
      for (J = 0; J < (1<<WIDTH); J++) begin : GEN_B_VAL
        localparam logic [WIDTH-1:0] AVAL = I;
        localparam logic [WIDTH-1:0] BVAL = J;
        cover property (@(a or b) ##0 (a == AVAL && b == BVAL && c === (AVAL & BVAL)));
      end
    end
  endgenerate

endmodule

// Bind into DUT
bind Vector Vector_sva #(.WIDTH(2)) u_vector_sva (.a(a), .b(b), .c(c));