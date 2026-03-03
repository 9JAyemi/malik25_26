// SVA for nonblocking_gate
// Checks full next-state functional equivalence and provides compact coverage.
// Bind this file alongside the DUT.

module nb_gate_sva (
  input logic         clk,
  input logic  [4:0]  ctrl,
  input logic  [1:0]  din,
  input logic  [0:0]  sel,
  input logic [31:0]  dout
);
  // Start flag to enable $past usage after first clock
  bit started;
  initial started = 1'b0;
  always @(posedge clk) started <= 1'b1;

  // Compute expected next-state per RTL nonblocking semantics
  function automatic logic [31:0] exp_next
    (input logic [31:0] prev,
     input logic  [4:0] ctrl_i,
     input logic        sel_i,
     input logic  [1:0] din_i);
    int unsigned k;
    logic [31:0] inc, low_mask, din_shift;
    begin
      k        = sel_i ? ctrl_i : 5'd0;
      inc      = prev + 32'd1;
      low_mask = (k == 0) ? 32'h0000_0000 : ((32'h1 << k) - 1); // keep [k-1:0]
      din_shift= {30'b0, din_i} << k;                          // place din at [k+1:k]
      exp_next = (inc & low_mask) | din_shift;                 // override [31:k]
    end
  endfunction

  // Functional equivalence: dout equals computed next-state
  property p_nextstate;
    @(posedge clk)
      started |-> dout == exp_next($past(dout), $past(ctrl), $past(sel[0]), $past(din));
  endproperty
  assert property (p_nextstate);

  // No-X on dout when inputs and prev dout are known
  property p_no_x;
    @(posedge clk)
      started && !$isunknown({$past(dout), $past(ctrl), $past(sel), $past(din)})
      |-> !$isunknown(dout);
  endproperty
  assert property (p_no_x);

  // Compact coverage: hit every case index when sel==1, plus sel==0, and edge cases
  genvar g;
  generate
    for (g = 0; g < 32; g++) begin : C_K
      cover property (@(posedge clk) started && ($past(sel)==1'b1) && ($past(ctrl)==g));
    end
  endgenerate
  // sel==0 path (forces k=0)
  cover property (@(posedge clk) started && ($past(sel)==1'b0) &&
                  dout == {30'b0, $past(din)});
  // k=31 truncation case: only bit31 overridden
  cover property (@(posedge clk) started && ($past(sel)==1'b1) && ($past(ctrl)==5'd31) &&
                  (dout[31] == $past(din[0])) &&
                  (dout[30:0] == ($past(dout)+32'd1)[30:0]));
endmodule

bind nonblocking_gate nb_gate_sva nb_gate_sva_i (.*);