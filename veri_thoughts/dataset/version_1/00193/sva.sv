// SVA checker for sky130_fd_sc_hd__a221oi
module sky130_fd_sc_hd__a221oi_sva (
  input logic A1,
  input logic A2,
  input logic B1,
  input logic B2,
  input logic C1,
  input logic Y
);

  default clocking cb @(A1 or A2 or B1 or B2 or C1 or Y); endclocking

  let termA     = (A1 & A2);
  let termB     = (B1 & B2);
  let expY      = ~(termA | termB | C1);
  let all_known = !$isunknown({A1,A2,B1,B2,C1});

  // Functional equivalence (4-state aware) once signals settle in the timestep
  assert property (all_known |-> ##0 (Y === expY));

  // Dominance checks
  assert property (all_known &&  C1    |-> ##0 (Y == 1'b0));
  assert property (all_known &&  termA |-> ##0 (Y == 1'b0));
  assert property (all_known &&  termB |-> ##0 (Y == 1'b0));
  assert property (all_known && !C1 && !termA && !termB |-> ##0 (Y == 1'b1));

  // X-propagation sanity: output X implies at least one input is X/Z
  assert property ($isunknown(Y) |-> !all_known);

  // Targeted functional coverage
  cover property (all_known ##0 (Y == 1'b1));
  cover property (all_known ##0 (Y == 1'b0));
  cover property (all_known && $rose(Y));
  cover property (all_known && $fell(Y));
  cover property (all_known &&  C1                       ##0 (Y == 1'b0));
  cover property (all_known &&  termA && !C1 && !termB   ##0 (Y == 1'b0));
  cover property (all_known &&  termB && !C1 && !termA   ##0 (Y == 1'b0));
  cover property (all_known && !C1 && !termA && !termB   ##0 (Y == 1'b1));

  // Full input-space coverage (all 32 input combinations at end-of-delta)
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : C_ALL_COMBOS
      localparam logic [4:0] v = i[4:0];
      cover property (##0 {A1,A2,B1,B2,C1} === v);
    end
  endgenerate

endmodule

// Bind into the DUT
bind sky130_fd_sc_hd__a221oi sky130_fd_sc_hd__a221oi_sva u_a221oi_sva (
  .A1(A1), .A2(A2), .B1(B1), .B2(B2), .C1(C1), .Y(Y)
);