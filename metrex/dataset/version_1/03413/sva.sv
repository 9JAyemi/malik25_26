// SVA checker for adder
module adder_sva #(parameter logic [3:0] B = 4'hA)
(
  input logic [3:0] A,
  input logic [3:0] S
);

  // Functional correctness (combinational settle with ##0)
  property sum_correct;
    @(A or S) 1 |-> ##0 (S === (A + B));
  endproperty
  assert property (sum_correct);

  // No X/Z on ports
  assert property (@(A) !$isunknown(A));
  assert property (@(S) !$isunknown(S));

  // Output changes only when input changes
  assert property (@(S) $changed(A));

  // Full functional coverage: see all 16 input values
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : cov_all_A
      localparam logic [3:0] Ai = i[3:0];
      cover property (@(A) A == Ai);
    end
  endgenerate

endmodule

// Bind to the DUT; B is captured from the target instance
bind adder adder_sva #(.B(B)) adder_sva_i (.A(A), .S(S));