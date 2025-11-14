// SVA for reversed_gate
// Bind this module to the DUT: bind reversed_gate reversed_gate_sva sva_i(.*);

module reversed_gate_sva (input logic clk,
                          input logic [4:0]  ctrl,
                          input logic [15:0] din,
                          input logic [3:0]  sel,
                          input logic [31:0] dout);

  // past-valid guard (no reset in DUT)
  logic past_valid;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Reproduce DUT index: idx = 31 - (ctrl*sel)
  logic [8:0] prod;
  logic signed [31:0] idx;
  assign prod = ctrl * sel;
  assign idx  = 32'sd31 - $signed({23'd0, prod});

  // Expected next dout (model of partial update)
  function automatic logic [31:0] expected_next(input logic [31:0] prev_dout,
                                                input logic signed [31:0] idx_f,
                                                input logic [15:0] din_f);
    logic [31:0] exp;
    exp = prev_dout;
    if ((idx_f >= 0) && (idx_f <= 31)) begin
      int w;
      w = (idx_f == 31) ? 1 : 2;
      exp[idx_f +: w] = din_f[w-1:0];
    end
    return exp;
  endfunction

  // 1) Robustness: no X on controlling/data inputs at sampling
  assert property (@(posedge clk) !$isunknown({ctrl, sel, din}))
    else $error("X/Z on ctrl/sel/din at clk edge");

  // 2) Functional equivalence: full next-state check (updates only correct slice; others hold)
  assert property (@(posedge clk) past_valid |-> dout == expected_next($past(dout), idx, din))
    else $error("dout next-state mismatch vs spec");

  // 3) When idx is out of [0..31], nothing updates (redundant with 2, but explicit)
  assert property (@(posedge clk) past_valid && (idx < 0) |-> $stable(dout))
    else $error("dout changed when no case item matched");

  // Coverage
  // a) Hit every case item 0..31 and observe the correct slice update
  genvar i;
  generate
    for (i = 0; i < 32; i++) begin : C_IDX
      localparam int W = (i==31) ? 1 : 2;
      cover property (@(posedge clk)
                      past_valid && (idx == i)
                      |=> dout[i +: W] == din[W-1:0]);
    end
  endgenerate

  // b) Exercise out-of-range (idx < 0) path where no assignment occurs
  cover property (@(posedge clk) past_valid && (idx < 0) |=> $stable(dout));

endmodule

// Bind example (place in a bind file or a separate compilation unit):
// bind reversed_gate reversed_gate_sva sva_i(.*);