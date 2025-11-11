// SVA for DEMUX — concise, high-quality checks and coverage
module DEMUX_sva #(
  parameter int n = 2
)(
  input  logic                 in,
  input  logic [n-1:0]         ctrl,
  input  logic [(1<<n)-1:0]    out
);
  localparam int W = (1<<n);

  // Golden combinational behavior (matches 4-state semantics of the RTL)
  always_comb begin
    logic [W-1:0] exp = '0;
    if (!$isunknown(ctrl)) exp[ctrl] = in;
    assert (out === exp)
      else $error("DEMUX mismatch: out=%b exp=%b in=%b ctrl=%0d", out, exp, in, ctrl);
  end

  // One-hot when in==1 and ctrl known
  always_comb if (!$isunknown(ctrl) && in===1'b1)
    assert ($onehot(out))
      else $error("DEMUX onehot failed: out=%b in=%b ctrl=%0d", out, in, ctrl);

  // All-zero when in==0 or ctrl unknown
  always_comb if (in===1'b0 || $isunknown(ctrl))
    assert (out=='0)
      else $error("DEMUX zeroing failed: out=%b in=%b ctrl=%b", out, in, ctrl);

  // No X/Z on outputs when inputs are known
  always_comb if (!$isunknown({in,ctrl}))
    assert (!$isunknown(out))
      else $error("DEMUX produced X/Z for known inputs: out=%b in=%b ctrl=%b", out, in, ctrl);

  // Coverage: each select hit with in=1; also in=0 case and X-ctrl safety
  genvar i;
  generate
    for (i=0; i<W; i++) begin : cov_sel
      always_comb cover (!$isunknown(ctrl) && ctrl==i && in===1'b1 && out[i]===1'b1);
    end
  endgenerate
  always_comb cover (!$isunknown(ctrl) && in===1'b0 && out=='0);
  always_comb cover ($isunknown(ctrl) && out=='0);
endmodule

// Bind into DUT
bind DEMUX DEMUX_sva #(.n(n)) demux_sva_i (.in(in), .ctrl(ctrl), .out(out));