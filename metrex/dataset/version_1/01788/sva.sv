// SVA checker for communication_module
module communication_module_sva (
  input logic A1, A2, A3, B1,
  input logic VPWR, VGND,
  input logic X
);
  default clocking cb @(A1 or A2 or A3 or B1 or X or VPWR or VGND); endclocking
  wire pgood = (VPWR === 1'b1) && (VGND === 1'b0);
  default disable iff (!pgood);

  wire [3:0] in = {A1, A2, A3, B1};
  wire       exp = (A1 & A2 & A3 & ~B1);

  // Functional equivalence (delta-cycle settled)
  assert property (@cb 1'b1 |-> ##0 (X === exp));

  // Output must not be X/Z when inputs are known
  assert property (@cb !($isunknown(in)) |-> ##0 !($isunknown(X)));

  // No glitches: inputs stable => output stable
  assert property (@cb $stable(in) |-> $stable(X));

  // Edge-cause checks
  assert property (@cb $rose(X) |-> exp);
  assert property (@cb $fell(X) |-> !exp);

  // Functional coverage
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : COV_IN_COMBOS
      cover property (@cb in == i[3:0]);
    end
  endgenerate
  cover property (@cb X === 1'b1);
  cover property (@cb X === 1'b0);
  cover property (@cb $rose(X));
  cover property (@cb $fell(X));
endmodule

// Bind into DUT
bind communication_module communication_module_sva u_comm_sva (
  .A1(A1), .A2(A2), .A3(A3), .B1(B1),
  .VPWR(VPWR), .VGND(VGND),
  .X(X)
);