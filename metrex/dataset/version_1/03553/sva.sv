// SVA for reset_test_gate
// Bindable checker focusing on concise, high-quality functional checks and key coverage

module reset_test_gate_sva (
  input logic        clk,
  input logic        reset,
  input logic [4:0]  ctrl,
  input logic [1:0]  din,
  input logic        sel,
  input logic [31:0] dout,
  input logic [1:0]  i,
  input logic        rval
);
  default clocking cb @(posedge clk); endclocking

  // Sanity checks
  assert property (rval == 1'b0);
  assert property ((|reset) == reset);
  assert property ($past(1'b1,1,1'b0) |-> !$isunknown({reset,ctrl,din,sel,dout}));

  // Golden next-state check for dout
  // k = ctrl*sel; upper slice [31:k] gets zero-extended din left-shifted by k;
  // lower [k-1:0] come from reset value (when reset) else $past(dout).
  property p_dout_next;
    logic [5:0]  k;
    logic [31:0] z, lowmask, lower, prev, expected;
    k       = ctrl * sel;
    z       = ({30'b0, din}) << k;
    prev    = $past(dout, 1, 32'd0);
    lowmask = (k==0) ? 32'h0 : ((32'h1 << k) - 1);
    lower   = (reset ? 32'd57005 : prev) & lowmask;
    expected= z | lower;
    dout == expected;
  endproperty
  assert property (p_dout_next) else $error("dout next-state mismatch");

  // Internal i behavior on reset
  assert property (reset |-> i == 2'b01);

  // Targeted functional checks (redundant with golden, but simple and focused)
  assert property ((sel==1'b0) |-> dout == {30'b0, din});                // full overwrite when sel=0
  assert property ((sel && ctrl==5'd0) |-> dout == {30'b0, din});        // also full overwrite when sel=1, ctrl=0

  // Coverage: reset path and key boundary cases (k=0,1,31)
  cover property ($rose(reset));
  cover property (reset && (ctrl*sel)==0 && dout=={30'b0,din});
  cover property (!reset && sel && ctrl==5'd1);
  cover property (!reset && sel && ctrl==5'd31);
  cover property (!reset && (ctrl*sel)==0 && din==2'b11);
endmodule

// Bind into the DUT
bind reset_test_gate reset_test_gate_sva sva(
  .clk  (clk),
  .reset(reset),
  .ctrl (ctrl),
  .din  (din),
  .sel  (sel),
  .dout (dout),
  .i    (i),
  .rval (rval)
);