// SVA for sky130_fd_sc_hd__nor4b
// Function: Y = ~ (A | B | C | ~D_N) = (~A & ~B & ~C & D_N)

module sky130_fd_sc_hd__nor4b_sva (
  input logic Y,
  input logic A,
  input logic B,
  input logic C,
  input logic D_N
);

  // Helpers
  let inputs_known = !$isunknown({A,B,C,D_N});
  let func_y      = (~A & ~B & ~C & D_N);

  // Functional equivalence (X-safe on inputs)
  // Triggers on any relevant signal change
  property p_func_eq;
    @(A or B or C or D_N or Y)
      inputs_known |-> (Y === func_y);
  endproperty
  assert property (p_func_eq);

  // Output must be known when inputs are known
  property p_y_known;
    @(A or B or C or D_N or Y)
      inputs_known |-> !$isunknown(Y);
  endproperty
  assert property (p_y_known);

  // Minimal toggle coverage on Y (under known inputs)
  cover property (@(A or B or C or D_N or Y) inputs_known && $rose(Y));
  cover property (@(A or B or C or D_N or Y) inputs_known && $fell(Y));

  // Full truth-table coverage (16 combinations), with correct Y
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : gen_tt_cov
      localparam logic [3:0] V = i[3:0]; // {A,B,C,D_N}
      cover property (
        @(A or B or C or D_N)
          inputs_known &&
          {A,B,C,D_N} == V &&
          (Y === (~V[3] & ~V[2] & ~V[1] & V[0]))
      );
    end
  endgenerate

endmodule

// Bind to all instances of the DUT
bind sky130_fd_sc_hd__nor4b sky130_fd_sc_hd__nor4b_sva u_sky130_fd_sc_hd__nor4b_sva (.*);