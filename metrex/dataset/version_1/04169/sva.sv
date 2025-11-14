// SVA for rising_edge_detector
module red_sva #(parameter int W=32) (
  input logic               clk,
  input logic               reset,
  input logic [W-1:0]       in,
  input logic [W-1:0]       out,
  input logic [W-1:0]       stage1_out,
  input logic [W-1:0]       stage2_out,
  input logic [W-1:0]       stage3_out
);

  default clocking cb @(posedge clk); endclocking

  // Helpers
  function automatic logic [W-1:0] rot1r (input logic [W-1:0] v);
    rot1r = {v[0], v[W-1:1]};
  endfunction
  function automatic logic [W-1:0] s2_of (input logic [W-1:0] v);
    s2_of = v ^ rot1r(v);
  endfunction
  function automatic logic [W-1:0] s3_of (input logic [W-1:0] v);
    s3_of = v & {~v[0], v[W-1:1]};
  endfunction

  // Reset clears on the cycle after reset was high
  assert property (@cb $past(reset) |-> (stage1_out=='0 && stage2_out=='0 && stage3_out=='0));

  // Functional checks (disabled while in reset)
  default disable iff (reset);

  // Pipeline stage checks
  assert property (@cb stage1_out == $past(in));
  assert property (@cb stage2_out == s2_of($past(stage1_out)));
  assert property (@cb stage3_out == s3_of($past(stage2_out)));

  // Output connectivity
  assert property (@cb out == stage3_out);

  // End-to-end: out is function of input two cycles earlier
  assert property (@cb $past(!reset,2) |-> stage3_out == s3_of(s2_of($past(in,2))));

  // Sanity for trivial inputs (all-0 or all-1 give zero out)
  assert property (@cb $past(!reset,2) && ($past(in,2) == '0)      |-> (stage3_out == '0));
  assert property (@cb $past(!reset,2) && ($past(in,2) == {W{1'b1}})|-> (stage3_out == '0));

  // Compact coverage
  cover property (@cb !reset ##1 (out != '0));
  cover property (@cb out[31]);
  cover property (@cb out[0]);
  cover property (@cb ($past(stage2_out[31]) && !$past(stage2_out[0])) && out[31]);

endmodule

bind rising_edge_detector red_sva #(.W(32)) u_red_sva (
  .clk(clk),
  .reset(reset),
  .in(in),
  .out(out),
  .stage1_out(stage1_out),
  .stage2_out(stage2_out),
  .stage3_out(stage3_out)
);