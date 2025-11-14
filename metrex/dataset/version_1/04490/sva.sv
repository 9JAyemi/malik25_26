// SVA for sky130_fd_sc_lp__o21bai (Y = ~(~B1_N & (A1 | A2)) = B1_N | (~A1 & ~A2))
module sky130_fd_sc_lp__o21bai_sva (
  input logic A1,
  input logic A2,
  input logic B1_N,
  input logic Y,
  input logic b,
  input logic or0_out,
  input logic nand0_out_Y
);
  function automatic logic expY(logic a1, logic a2, logic b1_n);
    return ~( (~b1_n) & (a1 | a2) );
  endfunction

  // Functional correctness for fully known inputs
  assert property (@(A1 or A2 or B1_N or Y)
    !$isunknown({A1,A2,B1_N}) |-> (Y === expY(A1,A2,B1_N))
  ) else $error("o21bai: Y mismatch for known inputs");

  // Deterministic-X behavior (must-resolve cases)
  assert property (@(A1 or A2 or B1_N) (B1_N === 1'b1) |-> (Y === 1'b1));
  assert property (@(A1 or A2 or B1_N) ((A1 === 1'b0) && (A2 === 1'b0)) |-> (Y === 1'b1));
  assert property (@(A1 or A2 or B1_N) ((B1_N === 1'b0) && (A1 === 1'b1 || A2 === 1'b1)) |-> (Y === 1'b0));

  // Internal net consistency
  assert property (@(B1_N or b)        b           === ~B1_N);
  assert property (@(A1 or A2 or or0_out) or0_out  === (A1 | A2));
  assert property (@(b or or0_out or nand0_out_Y)  nand0_out_Y === ~(b & or0_out));
  assert property (@(Y or nand0_out_Y) Y           === nand0_out_Y);

  // Full truth-table coverage (all 8 input combinations, with correct Y)
  genvar v;
  generate
    for (v = 0; v < 8; v++) begin : C_TT
      localparam logic [2:0] V = v[2:0]; // {A1,A2,B1_N}
      localparam logic EXPY = (V[0]) | ((~V[2]) & (~V[1]));
      cover property (@(A1 or A2 or B1_N or Y)
        ({A1,A2,B1_N} === V) && (Y === EXPY)
      );
    end
  endgenerate

  // Output toggles coverage
  cover property (@(A1 or A2 or B1_N or Y) $rose(Y));
  cover property (@(A1 or A2 or B1_N or Y) $fell(Y));
endmodule

bind sky130_fd_sc_lp__o21bai sky130_fd_sc_lp__o21bai_sva
  i_o21bai_sva (
    .A1(A1),
    .A2(A2),
    .B1_N(B1_N),
    .Y(Y),
    .b(b),
    .or0_out(or0_out),
    .nand0_out_Y(nand0_out_Y)
  );