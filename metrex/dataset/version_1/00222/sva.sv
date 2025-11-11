// SVA binders for top_module design hierarchy.
// Concise, high-signal-coverage, combinational checks with immediate assertions and covers.

// Checker for comb_circuit
module comb_circuit_sva(
  input  [15:0] in,
  input  [7:0]  out_hi,
  input  [7:0]  out_lo
);
  always @* begin
    // Functional equivalence
    assert (out_hi == in[15:8]) else $error("comb_circuit: out_hi != in[15:8]");
    assert (out_lo == in[7:0])  else $error("comb_circuit: out_lo != in[7:0]");

    // Knownness (only enforce when input is known)
    if (!$isunknown(in)) begin
      assert (!$isunknown(out_hi)) else $error("comb_circuit: out_hi has X/Z with known in");
      assert (!$isunknown(out_lo)) else $error("comb_circuit: out_lo has X/Z with known in");
    end
  end

  // Simple functional coverage
  cover (in == 16'h0000);
  cover (in == 16'hFFFF);
  cover (in[15:8] == 8'hFF && in[7:0] == 8'h00);
  cover (in[15:8] == 8'h00 && in[7:0] == 8'hFF);
endmodule

// Checker for mux_256to1
module mux_256to1_sva(
  input  [15:0] in,
  input  [7:0]  sel,
  input  [15:0] out
);
  // Local computed reference
  logic [15:0] ref_shift;
  always @* begin
    ref_shift = ((sel*8) >= 16) ? 16'h0000 : (in << (sel*8));

    // Knownness (only enforce when inputs are known)
    if (!$isunknown(in) && !$isunknown(sel)) begin
      assert (!$isunknown(out)) else $error("mux_256to1: out has X/Z with known in/sel");
    end

    // Exact functional check vs spec
    assert (out == ref_shift) else
      $error("mux_256to1: out != in << (sel*8) with saturation-to-zero");

    // Key corner-case refinements
    assert ((sel == 8'd0) -> (out == in)) else $error("mux_256to1: sel=0 case failed");
    assert ((sel == 8'd1) -> (out == {in[7:0],8'h00})) else $error("mux_256to1: sel=1 case failed");
    assert ((sel >=  8'd2) -> (out == 16'h0000)) else $error("mux_256to1: sel>=2 case failed");
  end

  // Coverage of select space and outputs
  cover (sel == 8'd0);
  cover (sel == 8'd1);
  cover (sel >= 8'd2);
  cover (out == 16'h0000);
endmodule

// Checker for adder
module adder_sva(
  input  [7:0]  in1,
  input  [7:0]  in2,
  input  [15:0] out
);
  logic [15:0] sum16;
  logic [8:0]  sum9;
  always @* begin
    sum16 = {8'h00, in1} + {8'h00, in2};
    sum9  = in1 + in2;

    // Knownness (only enforce when inputs are known)
    if (!$isunknown(in1) && !$isunknown(in2)) begin
      assert (!$isunknown(out)) else $error("adder: out has X/Z with known inputs");
    end

    // Functional equivalence
    assert (out == sum16) else $error("adder: out != zero-extended in1+in2");
    // Upper bits beyond carry must be zero
    assert (out[15:9] == 7'b0) else $error("adder: out[15:9] not zero");
    // Carry-out bit correctness
    assert (out[8] == sum9[8]) else $error("adder: carry-out mismatch");
  end

  // Corner-case coverage
  cover (in1==8'h00 && in2==8'h00 && out==16'h0000);
  cover (in1==8'hFF && in2==8'h00 && out==16'h00FF);
  cover (in1==8'hFF && in2==8'h01 && out==16'h0100); // carry
  cover (in1==8'hFF && in2==8'hFF && out==16'h01FE); // max sum
endmodule

// Optional top-level checker to sanity-check connectivity/visibility if desired
module top_module_sva(
  input  [15:0] in,
  input  [7:0]  out_hi,
  input  [7:0]  out_lo,
  input  [15:0] final_out
);
  // final_out must equal out_hi+out_lo (reinforces connectivity)
  logic [15:0] sum16;
  always @* begin
    sum16 = {8'h00,out_hi} + {8'h00,out_lo};
    assert (final_out == sum16) else $error("top: final_out != out_hi+out_lo");
  end

  // Coverage on adder carry via top visibility
  cover (out_hi + out_lo > 8'hFF);
endmodule

// Bind checkers into the DUT hierarchy
bind comb_circuit  comb_circuit_sva  comb_circuit_sva_i(.in(in), .out_hi(out_hi), .out_lo(out_lo));
bind mux_256to1    mux_256to1_sva    mux_256to1_sva_i(.in(in), .sel(sel), .out(out));
bind adder         adder_sva         adder_sva_i(.in1(in1), .in2(in2), .out(out));
bind top_module    top_module_sva    top_module_sva_i(.in(in), .out_hi(out_hi), .out_lo(out_lo), .final_out(final_out));