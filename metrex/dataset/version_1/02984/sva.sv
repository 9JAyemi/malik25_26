// SVA checker for barrel_shifter (16-bit circular barrel shifter)
// Bind or instantiate with a sampling clock.
module barrel_shifter_sva #(parameter W=16, parameter SW=$clog2(W)) (
  input logic                   clk,
  input logic [W-1:0]           data,
  input logic [SW-1:0]          shift_amount,
  input logic                   direction, // 1: left rotate, 0: right rotate
  input logic [W-1:0]           q
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [W-1:0] rotl(input logic [W-1:0] d, input logic [SW-1:0] s);
    int si = s;
    rotl = (si == 0) ? d : ((d << si) | (d >> (W - si)));
  endfunction

  function automatic logic [W-1:0] rotr(input logic [W-1:0] d, input logic [SW-1:0] s);
    int si = s;
    rotr = (si == 0) ? d : ((d >> si) | (d << (W - si)));
  endfunction

  // Functional correctness (inputs known => exact rotate result)
  property p_rotate_correct;
    !$isunknown({direction, shift_amount, data})
      |-> q == (direction ? rotl(data, shift_amount) : rotr(data, shift_amount));
  endproperty
  assert property (p_rotate_correct);

  // Zero shift is pass-through (both directions)
  assert property (!$isunknown({direction, shift_amount, data}) && shift_amount==0 |-> q==data);

  // Output must be known when inputs are known
  assert property (!$isunknown({direction, shift_amount, data}) |-> !$isunknown(q));

  // Stability: if inputs stable, output stable
  assert property ($stable({direction, shift_amount, data}) |-> $stable(q));

  // Invariant: rotation preserves number of 1s
  assert property (!$isunknown({direction, shift_amount, data}) |-> $countones(q) == $countones(data));

  // Coverage: hit every shift amount in both directions
  genvar s;
  generate
    for (s=0; s<W; s++) begin : COV_SHIFT
      cover property (!$isunknown({direction, shift_amount}) && direction && shift_amount==s);
      cover property (!$isunknown({direction, shift_amount}) && !direction && shift_amount==s);
    end
  endgenerate

  // Coverage: key data patterns and direction toggle
  cover property (data=='0 && shift_amount==0);
  cover property (data=={W{1'b1}} && shift_amount==0);
  cover property ($onehot(data));
  cover property (data==16'hAAAA || data==16'h5555);
  cover property (!$isunknown(direction) ##1 direction != $past(direction));

endmodule

// Example bind (place in a package or testbench):
// bind barrel_shifter barrel_shifter_sva bs_chk (.* , .clk(tb_clk));