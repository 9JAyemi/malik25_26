// SVA for mod4sum: checks modulo-4 sum correctness and covers inputs/outputs.
// Bind this module to the DUT.
module mod4sum_sva(input logic A, B, C, D, input logic [1:0] Y);

  default clocking cb @(posedge $global_clock); endclocking

  // 3-bit exact sum of the two 2-bit operands
  logic [2:0] sum3;
  always_comb sum3 = {1'b0,A,B} + {1'b0,C,D};

  // No X/Z on output when inputs are known
  property p_no_x;
    (!$isunknown({A,B,C,D})) |-> ##0 (!$isunknown(Y));
  endproperty
  assert property (p_no_x);

  // Functional correctness: Y equals sum modulo 4 (low 2 bits of sum3)
  property p_mod4_correct;
    disable iff ($isunknown({A,B,C,D,Y}))
      1'b1 |-> ##0 (Y == sum3[1:0]);
  endproperty
  assert property (p_mod4_correct);

  // Explicit branch checks + coverage: no-wrap and wrap cases
  property p_nowrap;
    disable iff ($isunknown({A,B,C,D,Y}))
      (sum3 < 3'd4) |-> ##0 (Y == sum3[1:0]);
  endproperty
  assert property (p_nowrap);
  cover  property (p_nowrap);

  property p_wrap;
    disable iff ($isunknown({A,B,C,D,Y}))
      (sum3 >= 3'd4) |-> ##0 (Y == (sum3 - 3'd4));
  endproperty
  assert property (p_wrap);
  cover  property (p_wrap);

  // Stability: with stable inputs, Y must remain stable
  property p_stable;
    disable iff ($isunknown({A,B,C,D,Y}))
      $stable({A,B,C,D}) |-> ##0 $stable(Y);
  endproperty
  assert property (p_stable);

  // Functional coverage: all input combinations and all output values
  genvar i;
  generate
    for (i = 0; i < 16; i++) begin : C_IN_ALL
      cover property ( {A,B,C,D} == i[3:0] );
    end
    for (i = 0; i < 4; i++) begin : C_OUT_ALL
      cover property ( Y == i[1:0] );
    end
  endgenerate

endmodule

bind mod4sum mod4sum_sva u_mod4sum_sva(.A(A), .B(B), .C(C), .D(D), .Y(Y));