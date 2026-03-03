// SVA for binary_adder and full_adder (bind these in your TB; provide clk/rst_n)

module binary_adder_sva(input logic clk, input logic rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z
  assert property (!$isunknown({A,B,CIN,S,COUT,sum,carry}));

  // Top-level arithmetic equivalence
  assert property ({COUT,S} == A + B + CIN);

  // Structural/ripple checks
  assert property (S == sum);

  assert property (sum[0]   == (A[0]^B[0]^CIN));
  assert property (carry[0] == ((A[0]&B[0]) | (CIN      & (A[0]^B[0]))));

  assert property (sum[1]   == (A[1]^B[1]^carry[0]));
  assert property (carry[1] == ((A[1]&B[1]) | (carry[0] & (A[1]^B[1]))));

  assert property (sum[2]   == (A[2]^B[2]^carry[1]));
  assert property (carry[2] == ((A[2]&B[2]) | (carry[1] & (A[2]^B[2]))));

  assert property (COUT     == ((A[3]&B[3]) | (carry[2] & (A[3]^B[3]))));

  // Concise functional coverage (key corners and behaviors)
  cover property ({A,B,CIN} == {4'h0,4'h0,1'b0} && {COUT,S} == 5'h00);
  cover property ({A,B,CIN} == {4'hF,4'hF,1'b1} && {COUT,S} == 5'h1F);
  cover property ((A^B)==4'hF && (A&B)==4'h0 && CIN==1'b0 && COUT==1'b0); // full propagate, no carry-in
  cover property ((A^B)==4'hF && (A&B)==4'h0 && CIN==1'b1 && COUT==1'b1); // full propagate, carry-in ripples out
  cover property (COUT==1'b1);
  cover property (COUT==1'b0);
endmodule

module full_adder_sva(input logic clk, input logic rst_n);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // No X/Z
  assert property (!$isunknown({A,B,CIN,S,COUT}));

  // Bit-accurate equivalence (redundant but strong)
  assert property ({COUT,S} == A + B + CIN);
  assert property (S        == (A^B^CIN));
  assert property (COUT     == ((A&B) | (CIN & (A^B))));

  // Cover all 8 input combinations per instance
  genvar i;
  for (i=0; i<8; i++) begin : c
    localparam logic [2:0] V = i[2:0];
    cover property ({A,B,CIN} == V);
  end
endmodule

bind binary_adder binary_adder_sva u_binary_adder_sva(.clk(clk), .rst_n(rst_n));
bind full_adder   full_adder_sva   u_full_adder_sva  (.clk(clk), .rst_n(rst_n));