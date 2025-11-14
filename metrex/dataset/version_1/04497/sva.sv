// SVA for six_to_one_rtl
module six_to_one_rtl_sva (
  input logic [4:0] A,
  input logic [1:0] B,
  input logic [7:0] X,
  input logic [3:0] sum1,
  input logic [2:0] sum2
);
  default clocking cb @(*); endclocking

  // Outputs/internal known if inputs known
  ap_known: assert property (!$isunknown({A,B})) |-> (!$isunknown({sum1,sum2,X}));

  // Internal gate correctness
  ap_s1_0: assert property (sum1[0] == ~(A[0] & A[1]));
  ap_s1_1: assert property (sum1[1] == ~(A[0] & A[2]));
  ap_s1_2: assert property (sum1[2] == ~(A[1] & A[2]));
  ap_s1_3: assert property (sum1[3] == ~(A[0] | A[1]));

  ap_s2_0: assert property (sum2[0] == ~(B[0] & B[1]));
  ap_s2_1: assert property (sum2[1] == ~(B[0] & sum1[3]));
  ap_s2_2: assert property (sum2[2] == ~(B[1] | sum1[3]));

  // Output gate correctness
  ap_x0: assert property (X[0] == ~(A[3] & A[4]));
  ap_x1: assert property (X[1] == ~(A[3] & sum2[2]));
  ap_x2: assert property (X[2] == ~(A[4] | sum2[2]));
  ap_x3: assert property (X[3] == ~(sum1[2] & sum2[1]));
  ap_x4: assert property (X[4] == ~(sum1[2] & sum2[0]));
  ap_x5: assert property (X[5] == ~(sum1[1] & sum2[1]));
  ap_x6: assert property (X[6] == ~(sum1[1] & sum2[0]));
  ap_x7: assert property (X[7] == ~(sum1[0] | sum2[1]));

  // Coverage: hit 0 and 1 on all observable nodes
  genvar i;
  generate
    for (i=0; i<8; i++) begin : cvX
      cover property (X[i] == 1'b0);
      cover property (X[i] == 1'b1);
    end
  endgenerate
  genvar j;
  generate
    for (j=0; j<4; j++) begin : cvS1
      cover property (sum1[j] == 1'b0);
      cover property (sum1[j] == 1'b1);
    end
  endgenerate
  genvar k;
  generate
    for (k=0; k<3; k++) begin : cvS2
      cover property (sum2[k] == 1'b0);
      cover property (sum2[k] == 1'b1);
    end
  endgenerate
endmodule

bind six_to_one_rtl six_to_one_rtl_sva sva_i (
  .A(A), .B(B), .X(X), .sum1(sum1), .sum2(sum2)
);