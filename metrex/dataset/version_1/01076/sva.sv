// SVA for decoder_3to8
// Bind this to the DUT and provide a clock/reset from your environment.

module decoder_3to8_sva (
  input logic        clk,
  input logic        rst_n,
  input logic  [2:0] A, B, C,
  input logic        EN,
  input logic  [7:0] Y
);
  default clocking cb @(posedge clk); endclocking
  default disable iff (!rst_n);

  // Outputs never X/Z when inputs are known
  assert property ( !$isunknown({EN,A,B,C}) |-> !$isunknown(Y) );

  // Global structural safety: at most one bit set (or zero)
  assert property ( $onehot0(Y) );

  // Functional decode as-implemented (note: case items are 3 bits)
  // EN low forces zero
  assert property ( !EN |-> (Y == 8'h00) );

  // EN high: only when A==0 and B==0 do we decode C; else default zero
  assert property ( EN && (A==3'b000) && (B==3'b000) |-> (Y == (8'b1 << C)) );
  assert property ( EN && ((A!=3'b000) || (B!=3'b000)) |-> (Y == 8'h00) );

  // Sanity: upper bits of A/B should be zero when enabled (width mismatch guard)
  assert property ( EN |-> (A[2:1]==2'b00 && B[2:1]==2'b00) )
    else $warning("decoder_3to8: A[2:1]/B[2:1] nonzero while EN=1; DUT ignores them due to 3-bit case items.");

  // Coverage: each decoded output, disabled zero, and default path
  genvar i;
  generate
    for (i=0; i<8; i++) begin : g_cov_bits
      cover property ( EN && A==3'b000 && B==3'b000 && C==i[2:0] && Y==(8'h1<<i) );
    end
  endgenerate
  cover property ( !EN && Y==8'h00 );
  cover property ( EN && (A!=3'b000 || B!=3'b000) && Y==8'h00 );

endmodule

// Example bind (provide clk/rst_n from your environment):
// bind decoder_3to8 decoder_3to8_sva u_decoder_3to8_sva(.clk(clk), .rst_n(rst_n), .A(A), .B(B), .C(C), .EN(EN), .Y(Y));