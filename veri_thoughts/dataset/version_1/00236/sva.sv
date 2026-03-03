// SVA for full_adder
module full_adder_sva (
    input logic A, B, CARRY_IN,
    input logic SUM, CARRY_OUT
);
  // Functional correctness (two equivalent forms)
  ap_fa_add: assert property ( {CARRY_OUT, SUM} == ({1'b0,A} + {1'b0,B} + {1'b0,CARRY_IN}) );
  ap_fa_bool: assert property (
      (SUM == (A ^ B ^ CARRY_IN)) &&
      (CARRY_OUT == ((A & B) | (A & CARRY_IN) | (B & CARRY_IN)))
  );

  // X-propagation: clean outputs if inputs are 0/1
  ap_fa_no_x: assert property ( !$isunknown({A,B,CARRY_IN}) |-> !$isunknown({SUM,CARRY_OUT}) );

  // Coverage: all input combinations
  cover property ( {A,B,CARRY_IN} == 3'b000 );
  cover property ( {A,B,CARRY_IN} == 3'b001 );
  cover property ( {A,B,CARRY_IN} == 3'b010 );
  cover property ( {A,B,CARRY_IN} == 3'b011 );
  cover property ( {A,B,CARRY_IN} == 3'b100 );
  cover property ( {A,B,CARRY_IN} == 3'b101 );
  cover property ( {A,B,CARRY_IN} == 3'b110 );
  cover property ( {A,B,CARRY_IN} == 3'b111 );
endmodule

bind full_adder full_adder_sva fa_sva (.*);


// SVA for four_bit_adder
module four_bit_adder_sva (
    input logic [3:0] A, B,
    input logic [3:0] OUT, SUM,
    input logic CARRY_OUT, CARRY_IN,
    input logic CO1, CO2, CO3
);
  // Overall correctness and wiring
  ap_total:      assert property ( {CARRY_OUT, OUT} == ({1'b0,A} + {1'b0,B} + {4'b0,CARRY_IN}) );
  ap_out_is_sum: assert property ( OUT == SUM );

  // Stage-by-stage ripple checks
  ap_s0: assert property ( {CO1,       SUM[0]} == ({1'b0,A[0]} + {1'b0,B[0]} + {1'b0,CARRY_IN}) );
  ap_s1: assert property ( {CO2,       SUM[1]} == ({1'b0,A[1]} + {1'b0,B[1]} + {1'b0,CO1}) );
  ap_s2: assert property ( {CO3,       SUM[2]} == ({1'b0,A[2]} + {1'b0,B[2]} + {1'b0,CO2}) );
  ap_s3: assert property ( {CARRY_OUT, SUM[3]} == ({1'b0,A[3]} + {1'b0,B[3]} + {1'b0,CO3}) );

  // X-propagation: clean outputs if inputs are 0/1
  ap_4b_no_x: assert property ( !$isunknown({A,B,CARRY_IN}) |-> !$isunknown({OUT,CARRY_OUT}) );

  // Coverage: extremes, propagate, generate, and kill scenarios
  cp_zero:      cover property ( A==4'h0 && B==4'h0 && CARRY_IN==1'b0 && CARRY_OUT==1'b0 && OUT==4'h0 );
  cp_max_ovf:   cover property ( A==4'hF && B==4'hF && CARRY_IN==1'b1 && CARRY_OUT==1'b1 && OUT==4'hF );
  cp_fullprop:  cover property ( (A ^ B)==4'hF && CARRY_IN==1'b1 && CARRY_OUT==1'b1 );
  cp_gen0:      cover property ( (A[0] & B[0]) && (CARRY_IN==1'b0) && CO1 );
  cp_gen1:      cover property ( (A[1] & B[1]) && (CO1==1'b0) && CO2 );
  cp_gen2:      cover property ( (A[2] & B[2]) && (CO2==1'b0) && CO3 );
  cp_gen3:      cover property ( (A[3] & B[3]) && (CO3==1'b0) && CARRY_OUT );
  cp_kill2:     cover property ( (A[2]==1'b0 && B[2]==1'b0) && (CO2==1'b1) && (CO3==1'b0) );
endmodule

bind four_bit_adder four_bit_adder_sva four_sva (
  .A(A), .B(B), .OUT(OUT), .SUM(SUM),
  .CARRY_IN(CARRY_IN), .CARRY_OUT(CARRY_OUT),
  .CO1(CO1), .CO2(CO2), .CO3(CO3)
);