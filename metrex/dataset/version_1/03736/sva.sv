// SVA checker for my_nor4
// Function implemented: Y == (A|B) & (C|D) when power-good

module my_nor4_sva (
  input logic A, B, C, D,
  input logic VPWR, VGND,
  input logic Y
);
  wire pwr_good = (VPWR === 1'b1) && (VGND === 1'b0);

  // Evaluate on any input/power change; use ##0 to avoid delta races
  default disable iff (!pwr_good);

  // Functional correctness (and X-prop safe)
  assert property (@(A or B or C or D or VPWR or VGND)
                   !$isunknown({A,B,C,D}) |-> ##0
                   (Y === ((A | B) & (C | D))))
    else $error("my_nor4: Y != (A|B)&(C|D)");

  // Output is known when inputs are known
  assert property (@(A or B or C or D or VPWR or VGND)
                   !$isunknown({A,B,C,D}) |-> ##0
                   !$isunknown(Y))
    else $error("my_nor4: Y is X/Z with known inputs");

  // Basic toggle coverage
  cover property (@(A or B or C or D) ##0 Y == 1'b1);
  cover property (@(A or B or C or D) ##0 Y == 1'b0);
  cover property (@(A or B or C or D or VPWR or VGND) $rose(Y));
  cover property (@(A or B or C or D or VPWR or VGND) $fell(Y));

  // Full truth-table coverage (all 16 minterms with expected Y)
  generate
    genvar i;
    for (i = 0; i < 16; i++) begin : g_tt
      localparam bit ai = (i >> 3) & 1;
      localparam bit bi = (i >> 2) & 1;
      localparam bit ci = (i >> 1) & 1;
      localparam bit di = (i >> 0) & 1;
      cover property (@(A or B or C or D)
                      A === ai && B === bi && C === ci && D === di
                      ##0 Y === (((ai | bi) & (ci | di))));
    end
  endgenerate
endmodule

// Bind into DUT
bind my_nor4 my_nor4_sva u_my_nor4_sva (
  .A(A), .B(B), .C(C), .D(D),
  .VPWR(VPWR), .VGND(VGND),
  .Y(Y)
);