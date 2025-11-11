// SVA binders for top_module and mux_2to1
// Focused, concise checks and coverage

// Top-level checker
module top_module_sva (
  input  logic [7:0] in,
  input  logic [1:0] sel,
  input  logic [1:0] sel_inv,
  input  logic [1:0] sel_2to1,
  input  logic [1:0] sel_inv_2to1,
  input  logic [1:0] mux1_out,
  input  logic [1:0] mux2_out,
  input  logic [1:0] mux3_out,
  input  logic [1:0] mux4_out,
  input  logic [3:0] out
);
  // Combinational, guard against Xs for meaningful checks
  always_comb begin
    // Structural wiring
    if (!$isunknown(sel)) begin
      assert (sel_inv        == ~sel) else $error("sel_inv != ~sel");
      assert (sel_2to1       ==  sel) else $error("sel_2to1 != sel");
      assert (sel_inv_2to1   == ~sel) else $error("sel_inv_2to1 != ~sel");
    end

    // Mux correctness and width/extension
    if (!$isunknown({in, sel})) begin
      assert (mux1_out == (sel[0] ? in[3:2] : in[1:0])) else $error("mux1_out wrong");
      assert (mux2_out == (sel[1] ? in[7:6] : in[5:4])) else $error("mux2_out wrong");
      assert (mux3_out == (sel[0] ? mux1_out : mux2_out)) else $error("mux3_out wrong (inv sel0)");
      assert (mux4_out == mux3_out) else $error("mux4_out must equal mux3_out");
      assert (out == {2'b00, mux4_out}) else $error("out must be zero-extended mux4_out");

      // Functional mapping (selected input slice -> out[1:0])
      if (sel == 2'b00) assert (out[1:0] == in[5:4]) else $error("sel=00 mapping wrong");
      if (sel == 2'b01) assert (out[1:0] == in[3:2]) else $error("sel=01 mapping wrong");
      if (sel == 2'b10) assert (out[1:0] == in[7:6]) else $error("sel=10 mapping wrong");
      if (sel == 2'b11) assert (out[1:0] == in[3:2]) else $error("sel=11 mapping wrong");

      // No-X on internal/outputs when inputs known
      assert (!$isunknown({sel_inv, sel_2to1, sel_inv_2to1,
                           mux1_out, mux2_out, mux3_out, mux4_out, out})) else
        $error("Unexpected X/Z on internal or out when inputs known");
    end

    // Concise coverage
    cover (!$isunknown({in, sel}) && sel==2'b00 && out[1:0]==in[5:4]);
    cover (!$isunknown({in, sel}) && sel==2'b01 && out[1:0]==in[3:2]);
    cover (!$isunknown({in, sel}) && sel==2'b10 && out[1:0]==in[7:6]);
    cover (!$isunknown({in, sel}) && sel==2'b11 && out[1:0]==in[3:2]);

    cover (sel[0]==0 && mux1_out==in[1:0]);
    cover (sel[0]==1 && mux1_out==in[3:2]);
    cover (sel[1]==0 && mux2_out==in[5:4]);
    cover (sel[1]==1 && mux2_out==in[7:6]);
  end
endmodule

bind top_module top_module_sva i_top_sva (
  .in(in), .sel(sel), .sel_inv(sel_inv),
  .sel_2to1(sel_2to1), .sel_inv_2to1(sel_inv_2to1),
  .mux1_out(mux1_out), .mux2_out(mux2_out),
  .mux3_out(mux3_out), .mux4_out(mux4_out), .out(out)
);

// Generic 2:1 mux checker
module mux_2to1_sva (
  input logic [1:0] in0,
  input logic [1:0] in1,
  input logic       sel,
  input logic [1:0] out
);
  always_comb begin
    if (!$isunknown({in0, in1, sel})) begin
      assert (out == (sel ? in1 : in0)) else $error("2:1 mux functional mismatch");
    end
    cover (sel==0 && out==in0);
    cover (sel==1 && out==in1);
  end
endmodule

bind mux_2to1 mux_2to1_sva i_mux_sva (.in0(in0), .in1(in1), .sel(sel), .out(out));