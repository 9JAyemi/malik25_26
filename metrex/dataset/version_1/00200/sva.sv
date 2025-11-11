// SVA for greater_than. Bind this to the DUT.
module greater_than_sva (
  input  logic [7:0] A,
  input  logic [7:0] B,
  input  logic [7:0] C,
  input  logic       Y
);

  // Functional equivalence with X-gating and same-tick sampling
  // Use ##0 to sample after combinational settle on input change
  property p_func_equiv;
    ##0 (!$isunknown({A,B,C})) |->
        ((Y == ((A >= B) && (C < B))) && !$isunknown(Y));
  endproperty
  assert property (@(A or B or C) p_func_equiv)
    else $error("Y != ((A >= B) && (C < B)) when inputs are known");

  // Basic functional coverage
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) && Y);
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) && !Y);

  // Boundary/edge-cover scenarios
  // A == B boundary and C just below B -> Y must be 1
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) &&
                  (A==B) && (C+8'd1==B) && Y);

  // C == B boundary -> Y must be 0
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) &&
                  (C==B) && !Y);

  // Extreme B == 0 -> C<B can never be true, so Y==0
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) &&
                  (B==8'h00) && !Y);

  // Extreme B == 255: Y iff A==255 and C!=255
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) &&
                  (B==8'hFF) && (A==8'hFF) && (C!=8'hFF) && Y);
  cover property (@(A or B or C) ##0 (!$isunknown({A,B,C})) &&
                  (B==8'hFF) && (C==8'hFF) && !Y);

endmodule

bind greater_than greater_than_sva u_greater_than_sva (.A(A), .B(B), .C(C), .Y(Y));