// SVA checker for five_to_one
module five_to_one_sva (
  input logic [1:0] in1,
  input logic [2:0] in2,
  input logic       in3,
  input logic [3:0] in4,
  input logic [1:0] in5,
  input logic       out1
);

  // No X/Z on DUT ports
  ap_no_x: assert property ( !$isunknown({in1,in2,in3,in4,in5,out1}) )
    else $error("five_to_one: X/Z detected on ports");

  // Functional equivalence
  ap_equiv: assert property ( out1 == ((in1>=2) || (in2>=4) || in3 || ((in4+in5)>=5)) )
    else $error("five_to_one: out1 does not match spec");

  // Feature coverage: each sole cause
  cp_in1_only: cover property ( (in1>=2) && (in2<4) && !in3 && ((in4+in5)<5) && out1 );
  cp_in2_only: cover property ( (in1<2) && (in2>=4) && !in3 && ((in4+in5)<5) && out1 );
  cp_in3_only: cover property ( (in1<2) && (in2<4) && in3 && ((in4+in5)<5) && out1 );
  cp_sum_only: cover property ( (in1<2) && (in2<4) && !in3 && ((in4+in5)>=5) && out1 );

  // None cause -> out1=0
  cp_none: cover property ( (in1<2) && (in2<4) && !in3 && ((in4+in5)<5) && !out1 );

  // Threshold boundaries
  cp_in1_eq2: cover property ( (in1==2) && (in2<4) && !in3 && ((in4+in5)<5) && out1 );
  cp_in1_eq1: cover property ( (in1==1) && (in2<4) && !in3 && ((in4+in5)<5) && !out1 );

  cp_in2_eq4: cover property ( (in1<2) && (in2==4) && !in3 && ((in4+in5)<5) && out1 );
  cp_in2_eq3: cover property ( (in1<2) && (in2==3) && !in3 && ((in4+in5)<5) && !out1 );

  cp_sum_eq5: cover property ( (in1<2) && (in2<4) && !in3 && ((in4+in5)==5) && out1 );
  cp_sum_eq4: cover property ( (in1<2) && (in2<4) && !in3 && ((in4+in5)==4) && !out1 );

endmodule

bind five_to_one five_to_one_sva u_five_to_one_sva (.*);