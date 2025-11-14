// SVA checker for hls_contrast_streibs_DSP48_6
module hls_contrast_streibs_DSP48_6_sva
(
  input       [7:0]   in0,
  input       [22:0]  in1,
  input       [31:0]  in2,
  input       [31:0]  dout,
  input  signed [24:0] a,
  input  signed [17:0] b,
  input  signed [47:0] c,
  input  signed [42:0] m,
  input  signed [47:0] p
);

  default clocking cb @(in0 or in1 or in2); endclocking

  // Reference model (pure combinational, sized, signed)
  logic signed [24:0] a_ref;
  logic signed [17:0] b_ref;
  logic signed [47:0] c_ref;
  logic signed [42:0] m_ref;
  logic signed [47:0] p_ref;

  always_comb begin
    a_ref = $signed(in1);     // sign-extend 23->25
    b_ref = $signed(in0);     // sign-extend 8->18
    c_ref = $signed(in2);     // sign-extend 32->48
    m_ref = a_ref * b_ref;    // 25*18 -> 43
    p_ref = m_ref + c_ref;    // 43 + 48 -> 48
  end

  // End-to-end functional equivalence and no-X check (when inputs known)
  assert property ( !$isunknown({in0,in1,in2}) |->
                    (a == a_ref) && (b == b_ref) && (c == c_ref) &&
                    (m == m_ref) && (p == p_ref) &&
                    (dout == p_ref[31:0]) );

  // If the 48-bit sum fits in 32-bit signed, dout sign-extends back to p_ref
  assert property ( !$isunknown({in0,in1,in2}) &&
                    (p_ref[47:32] == {16{p_ref[31]}}) |->
                    $signed({{16{dout[31]}}, dout}) == p_ref );

  // Coverage: observe truncation/overflow cases and corner stimuli
  cover property ( !$isunknown({in0,in1,in2}) &&
                   (|(p_ref[47:32] ^ {16{p_ref[31]}})) ); // 32-bit overflow/truncation occurred
  cover property ( a_ref < 0 && b_ref > 0 );
  cover property ( a_ref > 0 && b_ref < 0 );
  cover property ( (a_ref == 0) || (b_ref == 0) );
  cover property ( p_ref == 0 );
  cover property ( p_ref < 0 );
  cover property ( p_ref > 0 );
  cover property ( in0 == 8'h80 || in0 == 8'h7F );
  cover property ( in1 == 23'h400000 || in1 == 23'h3FFFFF );
  cover property ( in2 == 32'h80000000 || in2 == 32'h7FFFFFFF );

endmodule

// Bind into DUT (connects ports by matching names, including internals a/b/c/m/p)
bind hls_contrast_streibs_DSP48_6 hls_contrast_streibs_DSP48_6_sva sva_i (.*);