// SVA checkers and binds for top_module, mux_2to1, signed_mag_comp

`ifndef TOP_MODULE_SVA
`define TOP_MODULE_SVA

// Top-level checker
module top_module_sva (
  input  signed [3:0] A,
  input  signed [3:0] B,
  input               sel,
  input               C,
  input  signed [3:0] mux_output,
  input         [0:0] mag_comp_output
);
  // Combinational correctness and X-prop
  always @* begin
    if (!$isunknown({A,B,sel})) assert (!$isunknown(C)) else $error("C is X/Z with known inputs");
    assert (mag_comp_output === (A===B)) else $error("mag_comp_output != (A==B)");
    assert (mux_output      === (sel ? A : B)) else $error("mux_output != (sel?A:B)");
    if (sel==1'b0) assert (C === (A===B)) else $error("C mismatch when sel=0");
    else           assert (C === mux_output[0]) else $error("C mismatch when sel=1");
  end

  // Minimal functional coverage
  always @* begin
    cover (sel==1'b0 && (A===B) && C===1'b1);
    cover (sel==1'b0 && (A!==B) && C===1'b0);
    cover (sel==1'b1 && C===A[0]);
    cover (sel==1'b0 && A > B);
    cover (sel==1'b0 && A < B);
  end
endmodule

bind top_module top_module_sva (.A(A), .B(B), .sel(sel), .C(C), .mux_output(mux_output), .mag_comp_output(mag_comp_output));

// Mux checker
module mux_2to1_sva (
  input [7:0] in,
  input       sel,
  input [3:0] out
);
  always @* begin
    if (!$isunknown({in,sel})) assert (!$isunknown(out)) else $error("mux out X/Z with known in/sel");
    assert (out === (sel ? in[7:4] : in[3:0])) else $error("mux out wrong");
  end
  always @* begin
    cover (sel==1'b0 && out===in[3:0]);
    cover (sel==1'b1 && out===in[7:4]);
  end
endmodule

bind mux_2to1 mux_2to1_sva (.*);

// Comparator checker
module signed_mag_comp_sva (
  input  signed [3:0] A,
  input  signed [3:0] B,
  input         [0:0] C
);
  always @* begin
    if (!$isunknown({A,B})) assert (!$isunknown(C)) else $error("comp C X/Z with known A/B");
    assert (C === (A===B)) else $error("comp C should be 1 only when A==B");
  end
  always @* begin
    cover (A===B && C===1'b1);
    cover (A > B && C===1'b0);
    cover (A < B && C===1'b0);
  end
endmodule

bind signed_mag_comp signed_mag_comp_sva (.*);

`endif