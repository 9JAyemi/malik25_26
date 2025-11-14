// SVA for the given design. Bind these checkers to the DUT.
// Focused, concise, and covers key functionality and integration.

/////////////////////////////////////////////////////////////
// mux4to1_decoder SVA
/////////////////////////////////////////////////////////////
module mux4to1_decoder_sva(
  input [3:0]  sel,
  input [15:0] in,
  input [15:0] out
);
  // Expected zero-extended mask of low (16-sel) bits
  function automatic [15:0] mask16(input [3:0] s);
    mask16 = ((16'h1 << (5'd16 - s)) - 16'h1);
  endfunction

  always_comb begin
    // Inputs known
    assert (!$isunknown({sel,in})) else $error("mux4to1_decoder: X on inputs");
    // Functional check
    if (!$isunknown({sel,in}))
      assert (out == (in & mask16(sel)))
        else $error("mux4to1_decoder: out mismatch for sel=%0d", sel);
    // Output known when inputs known
    if (!$isunknown({sel,in}))
      assert (!$isunknown(out)) else $error("mux4to1_decoder: X on out");
  end

  // Coverage: hit all sel values
  genvar k;
  generate
    for (k=0; k<16; k++) begin : COV_SEL
      always_comb cover (sel == k[3:0]);
    end
  endgenerate
  // Coverage: some structural edges
  always_comb begin
    cover (sel == 4'd0);
    cover (sel == 4'd15);
  end
endmodule

bind mux4to1_decoder mux4to1_decoder_sva mux4to1_decoder_sva_i(.*);

/////////////////////////////////////////////////////////////
// count_zeros SVA
/////////////////////////////////////////////////////////////
module count_zeros_sva(
  input [255:0] in,
  input         out
);
  // out should be odd parity of in (since 256 is even)
  logic parity_in;
  always_comb begin
    parity_in = ^in;
    // Inputs known -> parity must match
    if (!$isunknown(in))
      assert (out == parity_in)
        else $error("count_zeros: out != ^in");
    // Output known when inputs known
    if (!$isunknown(in))
      assert (!$isunknown(out)) else $error("count_zeros: X on out");
  end

  // Coverage: exercise both parities and extremes
  always_comb begin
    if (!$isunknown(in)) begin
      cover (parity_in == 1'b0);
      cover (parity_in == 1'b1);
    end
    cover (in == '0); // all zeros
    cover (in == '1); // all ones
  end
endmodule

bind count_zeros count_zeros_sva count_zeros_sva_i(.*);

/////////////////////////////////////////////////////////////
// bitwise_or SVA
/////////////////////////////////////////////////////////////
module bitwise_or_sva(
  input in1,
  input in2,
  input out
);
  always_comb begin
    if (!$isunknown({in1,in2}))
      assert (out == (in1 | in2))
        else $error("bitwise_or: out != in1|in2");
    if (!$isunknown({in1,in2}))
      assert (!$isunknown(out)) else $error("bitwise_or: X on out");
  end

  // Coverage: all input combinations and both output values
  always_comb begin
    cover ({in1,in2} == 2'b00 && out==1'b0);
    cover ({in1,in2} == 2'b01 && out==1'b1);
    cover ({in1,in2} == 2'b10 && out==1'b1);
    cover ({in1,in2} == 2'b11 && out==1'b1);
  end
endmodule

bind bitwise_or bitwise_or_sva bitwise_or_sva_i(.*);

/////////////////////////////////////////////////////////////
// top_module SVA (end-to-end integration)
/////////////////////////////////////////////////////////////
module top_module_sva(
  input [255:0] in,
  input [3:0]   sel,
  input [15:0]  mux_out,
  input         count_out,
  input         out
);
  function automatic [15:0] mask16(input [3:0] s);
    mask16 = ((16'h1 << (5'd16 - s)) - 16'h1);
  endfunction

  // Expected mux input packing from top wiring
  function automatic [15:0] packed_from_in(input [255:0] din);
    packed_from_in = {din[3:0], din[7:4], din[11:8], din[15:12]};
  endfunction

  logic [15:0] exp_mux_out;
  logic        exp_count_out;
  logic        exp_top_out;

  always_comb begin
    exp_mux_out   = packed_from_in(in) & mask16(sel);
    exp_count_out = ^in;
    exp_top_out   = (exp_mux_out[0] | exp_count_out);

    if (!$isunknown({in,sel})) begin
      // Mux path equivalence
      assert (mux_out == exp_mux_out)
        else $error("top: mux_out mismatch");
      // Count path equivalence
      assert (count_out == exp_count_out)
        else $error("top: count_out mismatch");
      // Final OR output equivalence
      assert (out == exp_top_out)
        else $error("top: out mismatch");
      // Knownness
      assert (!$isunknown({mux_out,count_out,out}))
        else $error("top: X on internal/output");
    end
  end

  // Coverage: mux select extremes and OR truth table at output
  always_comb begin
    cover (sel == 4'd0);
    cover (sel == 4'd15);
    // Drive OR truth table via observed internal signals
    if (!$isunknown({mux_out[0],(^in)})) begin
      cover ({mux_out[0],(^in)} == 2'b00 && out==1'b0);
      cover ({mux_out[0],(^in)} == 2'b01 && out==1'b1);
      cover ({mux_out[0],(^in)} == 2'b10 && out==1'b1);
      cover ({mux_out[0],(^in)} == 2'b11 && out==1'b1);
    end
  end
endmodule

bind top_module top_module_sva top_module_sva_i(
  .in(in),
  .sel(sel),
  .mux_out(mux_out),
  .count_out(count_out),
  .out(out)
);