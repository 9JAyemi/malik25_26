// SVA for comparator. Bind this file to the DUT.
module comparator_sva(input logic [1:0] A, B, input logic Z);

  // Gate checks to known inputs
  always_comb begin
    if (!$isunknown({A,B})) begin
      automatic bit msb_gt = (A[1] > B[1]);
      automatic bit msb_lt = (A[1] < B[1]);
      automatic bit msb_eq = (A[1] == B[1]);
      automatic bit lsb_gt = (A[0] > B[0]);
      automatic bit lsb_lt = (A[0] < B[0]);
      automatic bit eq     = (A == B);

      // Functional correctness (matches intended -1/0/+1 behavior)
      if (msb_gt)                    assert (Z == 1)          else $error("Z != +1 when A[1]>B[1] (A=%b B=%b Z=%b)",A,B,Z);
      if (msb_lt)                    assert (Z === 2'sb11)     else $error("Z != -1 when A[1]<B[1] (A=%b B=%b Z=%b)",A,B,Z);
      if (msb_eq && lsb_gt)          assert (Z == 1)          else $error("Z != +1 when A[0]>B[0] (A=%b B=%b Z=%b)",A,B,Z);
      if (msb_eq && lsb_lt)          assert (Z === 2'sb11)     else $error("Z != -1 when A[0]<B[0] (A=%b B=%b Z=%b)",A,B,Z);
      if (eq)                        assert (Z == 0)          else $error("Z != 0 when A==B (A=%b B=%b Z=%b)",A,B,Z);

      // Knownness: known inputs must yield known output
      assert (!$isunknown(Z)) else $error("Z is X/Z for known inputs (A=%b B=%b Z=%b)",A,B,Z);

      // Branch coverage (exercise every decision arm)
      cover (msb_gt && (Z==1));
      cover (msb_lt && (Z===2'sb11));
      cover (msb_eq && lsb_gt && (Z==1));
      cover (msb_eq && lsb_lt && (Z===2'sb11));
      cover (eq && (Z==0));
    end
  end

  // Input space coverage (all 16 A/B combinations)
  genvar i,j;
  generate
    for (i=0;i<4;i++) begin : gA
      for (j=0;j<4;j++) begin : gB
        always_comb cover ((A==i[1:0]) && (B==j[1:0]));
      end
    end
  endgenerate

endmodule

bind comparator comparator_sva u_comparator_sva(.A(A), .B(B), .Z(Z));