// SVA for module counter
module counter_sva(input logic clk, rst, input logic [3:0] out);

  default clocking cb @(posedge clk); endclocking

  // Track availability of $past
  logic past_valid;
  initial past_valid = 1'b0;
  always @(posedge clk) past_valid <= 1'b1;

  // No X/Z on key observations
  assert property (cb !$isunknown({rst,out}));
  assert property (@(posedge rst) ##0 !$isunknown(out));

  // Asynchronous reset clears immediately
  assert property (@(posedge rst) ##0 (out == 4'h0));

  // While reset is asserted, output becomes and stays zero
  assert property (cb rst |=> out == 4'h0);
  assert property (cb rst && $past(rst) |-> out == 4'h0);

  // Functional counting (includes first cycle after reset release)
  assert property (cb disable iff (!past_valid || rst)
                   out == (($past(out)==4'hF) ? 4'h0 : ($past(out)+4'h1)));

  // First clock after reset deassert goes to 1
  assert property (cb (!rst && $past(rst)) |-> out == 4'h1);

  // Explicit wrap check
  assert property (cb disable iff (rst) ($past(out)==4'hF) |-> out==4'h0);

  // Coverage
  cover property (cb $rose(rst));
  cover property (cb $fell(rst));
  cover property (cb disable iff (rst) (out==4'hE ##1 out==4'hF ##1 out==4'h0 ##1 out==4'h1));

endmodule

bind counter counter_sva u_counter_sva(.clk(clk), .rst(rst), .out(out));