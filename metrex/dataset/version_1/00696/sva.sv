// SVA checker for sky130_fd_sc_hd__o2bb2a
module sky130_fd_sc_hd__o2bb2a_sva (
  input logic A1_N,
  input logic A2_N,
  input logic B1,
  input logic B2,
  input logic X,
  // internal nets (bound to DUT wires)
  input logic nand0_out,
  input logic or0_out,
  input logic and0_out_X
);

  default clocking cb @(*); endclocking

  // Helpers
  let known_in     = !$isunknown({A1_N, A2_N, B1, B2});
  let B_or         = (B1 | B2);
  let A_nand       = ~(A1_N & A2_N);
  let X_func       = A_nand & B_or;

  // No X on outputs/internal when inputs known
  assert property (known_in |-> ##0 !$isunknown({nand0_out, or0_out, and0_out_X, X}));

  // Structural equivalence of internal nets
  assert property (known_in |-> ##0 (nand0_out   == A_nand));
  assert property (known_in |-> ##0 (or0_out     == B_or));
  assert property (known_in |-> ##0 (and0_out_X  == (nand0_out & or0_out)));
  assert property (1'b1     |-> ##0 (X           == and0_out_X));

  // Functional equivalence of output
  assert property (known_in |-> ##0 (X == X_func));

  // Key gating behaviors
  assert property (known_in && (B_or==1'b0) |-> ##0 (X==1'b0));            // B gate off forces 0
  assert property (known_in && (A1_N & A2_N) |-> ##0 (X==1'b0));           // both A_N high forces 0
  assert property (known_in && (B_or==1'b1) && (A_nand==1'b1) |-> ##0 (X)); // both enables true gives 1

  // Coverage: X=0, X=1, and toggles
  cover property (known_in && (X==1'b0));
  cover property (known_in && (X==1'b1));
  cover property (known_in && $rose(X));
  cover property (known_in && $fell(X));

  // Compact full input-space coverage (all 16 combinations)
  generate
    genvar v;
    for (v=0; v<16; v++) begin : COV_ALL_INPUTS
      cover property ( {A1_N,A2_N,B1,B2} == v[3:0] );
    end
  endgenerate

endmodule

// Bind into the DUT, including internal wires for precise checking
bind sky130_fd_sc_hd__o2bb2a sky130_fd_sc_hd__o2bb2a_sva u_sva (
  .A1_N(A1_N),
  .A2_N(A2_N),
  .B1(B1),
  .B2(B2),
  .X(X),
  .nand0_out(nand0_out),
  .or0_out(or0_out),
  .and0_out_X(and0_out_X)
);