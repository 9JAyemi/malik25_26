// SVA for multiplier_module
// Checks 1-cycle functional correctness (mod 256), reset behavior, X-prop, and key corner cases.
module multiplier_module_sva (
  input logic        clk,
  input logic        rst,
  input logic [3:0]  a,b,c,d,
  input logic [7:0]  out
);

  // Functional correctness: out at N equals (a*b*c*d)[7:0] from N-1 when not in reset
  property p_mult_pipeline;
    @(posedge clk)
      (!rst && !$past(rst)) |-> out == ($past(a)*$past(b)*$past(c)*$past(d))[7:0];
  endproperty
  assert property (p_mult_pipeline);

  // Reset: next cycle zero, and hold zero while reset stays high
  property p_reset_next_zero;
    @(posedge clk) rst |=> out == 8'h00;
  endproperty
  assert property (p_reset_next_zero);

  property p_reset_hold_zero;
    @(posedge clk) (rst && $past(rst)) |-> out == 8'h00;
  endproperty
  assert property (p_reset_hold_zero);

  // No X/Z during active operation
  assert property (@(posedge clk) !rst |-> !$isunknown({a,b,c,d,out}));

  // Corner case: any zero operand -> zero result next cycle
  assert property (@(posedge clk)
    (!rst && !$past(rst) &&
     (($past(a)==4'h0) || ($past(b)==4'h0) || ($past(c)==4'h0) || ($past(d)==4'h0)))
    |-> (out == 8'h00));

  // Coverage
  cover property (@(posedge clk) rst ##1 !rst); // reset pulse seen
  cover property (@(posedge clk) !rst && !$past(rst) &&
                  (($past(a)*$past(b)*$past(c)*$past(d)) <= 16'd255)); // no overflow
  cover property (@(posedge clk) !rst && !$past(rst) &&
                  (($past(a)*$past(b)*$past(c)*$past(d)) > 16'd255));  // overflow/truncation
  cover property (@(posedge clk) !rst && !$past(rst) &&
                  ($past(a)==4'hF && $past(b)==4'hF && $past(c)==4'hF && $past(d)==4'hF) &&
                  out==8'hC1); // 15*15*15*15 mod 256
endmodule

bind multiplier_module multiplier_module_sva sva_i (.*);