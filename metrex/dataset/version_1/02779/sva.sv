// SVA for counter_module
module counter_module_sva(
  input logic        clk,
  input logic        rst,
  input logic        en,
  input logic [3:0]  count
);
  default clocking cb @(posedge clk); endclocking

  // Track $past validity
  logic past_valid;
  initial past_valid = 1'b0;
  always_ff @(posedge clk) past_valid <= 1'b1;

  // Basic correctness
  a_reset_zero: assert property (cb rst |-> (count == 4'h0));

  a_inc: assert property (cb disable iff (!past_valid)
                          (!rst && en) |-> (($past(count) != 4'hF) ? (count == $past(count)+1) : (count == 4'h0)));

  a_hold: assert property (cb disable iff (!past_valid)
                           (!rst && !en) |-> (count == $past(count)));

  // Sanity: no X/Z on key signals after first cycle
  a_no_xz: assert property (cb disable iff (!past_valid)
                            !$isunknown({rst,en,count}));

  // Coverage
  c_reset:        cover property (cb rst);
  c_deassert:     cover property (cb $fell(rst));
  c_inc:          cover property (cb !rst && en);
  c_hold:         cover property (cb disable iff (!past_valid) !rst && !en && (count == $past(count)));
  c_wrap:         cover property (cb disable iff (!past_valid) (!rst && en && ($past(count) == 4'hF) && (count == 4'h0)));
  c_after_reset_inc: cover property (cb rst ##1 (!rst && en));
endmodule

// Bind into DUT
bind counter_module counter_module_sva sva_i (.clk(clk), .rst(rst), .en(en), .count(count));