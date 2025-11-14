// Concise, high-quality SVA for Adder
// Bind this checker to the DUT: bind Adder Adder_sva #(4) u_adder_sva (.*);

module Adder_sva #(parameter int W=4)
(
  input logic               clk,
  input logic               rst,
  input logic               load,
  input logic [W-1:0]       A,
  input logic [W-1:0]       B,
  input logic [W-1:0]       Q
);

  default clocking cb @(posedge clk); endclocking

  function automatic logic [W-1:0] low_sum(input logic [W-1:0] a,b);
    logic [W:0] tmp; tmp = {1'b0,a} + {1'b0,b}; return tmp[W-1:0];
  endfunction
  function automatic logic          carry  (input logic [W-1:0] a,b);
    logic [W:0] tmp; tmp = {1'b0,a} + {1'b0,b}; return tmp[W];
  endfunction

  // Basic correctness
  property p_reset_next_zero; rst |=> (Q == '0); endproperty
  property p_hold_when_no_load; (!rst && !load) |=> (Q == $past(Q)); endproperty
  property p_load_captures_sum; (!rst && load)  |=> (Q == $past(low_sum(A,B))); endproperty

  // Sanity: no X/Z when active
  property p_no_x_rst; !$isunknown(rst); endproperty
  property p_no_x_in_active; (!rst) |-> !$isunknown({load,A,B}); endproperty
  property p_no_x_out_active; (!rst && !$isunknown({load,A,B})) |-> !$isunknown(Q); endproperty

  // Assert
  assert property (p_reset_next_zero);
  assert property (p_hold_when_no_load);
  assert property (p_load_captures_sum);
  assert property (p_no_x_rst);
  assert property (p_no_x_in_active);
  assert property (p_no_x_out_active);

  // Cover: reset, normal load, wrap-around, hold behavior, extremes
  cover property (rst ##1 !rst ##1 load);
  cover property (!rst && load && !carry(A,B));
  cover property (!rst && load &&  carry(A,B));               // overflow/wrap
  cover property (!rst && !load ##1 !rst && !load);           // hold over 2 cycles
  cover property (!rst && load && (A==0)  && (B==0));
  cover property (!rst && load && (A=='1) && (B=='1));        // 0xF + 0xF

endmodule