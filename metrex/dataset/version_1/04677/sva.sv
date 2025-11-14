// SVA checker for WF. Bind this to the DUT.
// Focus: functional equivalence, X-prop checks, and concise functional coverage.

module wf_sva (
  input  logic        i_op,
  input  logic [63:0] i_wf_in,
  input  logic [31:0] i_wk,
  input  logic [63:0] o_wf_out
);

  // Expected transformation (byte-wise)
  logic [7:0] b7, b6, b5, b4, b3, b2, b1, b0;
  assign b7 = i_wf_in[63:56];
  assign b6 = i_wf_in[55:48] ^ i_wk[31:24];
  assign b5 = i_wf_in[47:40];
  assign b4 = (i_op == 1'b0) ? (i_wf_in[39:32] + i_wk[23:16])
                             : (i_wf_in[39:32] - i_wk[23:16]);
  assign b3 = i_wf_in[31:24];
  assign b2 = i_wf_in[23:16] ^ i_wk[15:8];
  assign b1 = i_wf_in[15:8];
  assign b0 = (i_op == 1'b0) ? (i_wf_in[7:0] + i_wk[7:0])
                             : (i_wf_in[7:0] - i_wk[7:0]);

  logic [63:0] exp;
  assign exp = {b7,b6,b5,b4,b3,b2,b1,b0};

  // Core functional assertion and X/Z robustness
  always_comb begin
    assert (o_wf_out === exp)
      else $error("WF: functional mismatch. exp=%0h got=%0h", exp, o_wf_out);

    if (!$isunknown({i_op,i_wf_in,i_wk}))
      assert (!$isunknown(o_wf_out))
        else $error("WF: X/Z on output with known inputs.");
  end

  // Concise functional coverage (immediate cover)
  // Mode coverage
  always_comb begin
    cover (i_op == 1'b0);
    cover (i_op == 1'b1);
  end

  // Addition wrap-around (carry) coverage
  always_comb begin
    cover ((i_op==1'b0) && ((i_wf_in[39:32] + i_wk[23:16]) < i_wf_in[39:32]));
    cover ((i_op==1'b0) && ((i_wf_in[7:0]   + i_wk[7:0])   < i_wf_in[7:0]));
  end

  // Subtraction wrap-around (borrow) coverage
  always_comb begin
    cover ((i_op==1'b1) && (i_wf_in[39:32] < i_wk[23:16]));
    cover ((i_op==1'b1) && (i_wf_in[7:0]   < i_wk[7:0]));
  end

  // XOR corner coverage: unchanged (key=0) and full invert (key=FF) for both XOR bytes
  always_comb begin
    cover ((i_wk[31:24]==8'h00) && (o_wf_out[55:48]==i_wf_in[55:48]));
    cover ((i_wk[31:24]==8'hFF) && (o_wf_out[55:48]==~i_wf_in[55:48]));
    cover ((i_wk[15:8] ==8'h00) && (o_wf_out[23:16]==i_wf_in[23:16]));
    cover ((i_wk[15:8] ==8'hFF) && (o_wf_out[23:16]==~i_wf_in[23:16]));
  end

endmodule

// Bind into DUT
bind WF wf_sva u_wf_sva (
  .i_op(i_op),
  .i_wf_in(i_wf_in),
  .i_wk(i_wk),
  .o_wf_out(o_wf_out)
);