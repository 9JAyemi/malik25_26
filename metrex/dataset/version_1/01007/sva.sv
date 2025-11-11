// SVA for adder_block
// Bindable, clockless via $global_clock, concise yet comprehensive

module adder_block_sva #(parameter int WIDTH = 32)
(
  input logic [WIDTH-1:0] i_data0,
  input logic [WIDTH-1:0] i_data1,
  input logic [WIDTH-1:0] o_data0
);

  default clocking cb @(posedge $global_clock); endclocking

  // Common expression
  let sum = i_data0 + i_data1;

  // Functional correctness (mod 2^WIDTH) when inputs are known
  a_func: assert property ( ! $isunknown({i_data0,i_data1}) |-> (o_data0 == sum) );

  // Output must not be X/Z when inputs are known
  a_no_x_out: assert property ( ! $isunknown({i_data0,i_data1}) |-> ! $isunknown(o_data0) );

  // Combinational stability: if inputs don’t change (and are known), output doesn’t change
  a_stable: assert property ( (! $isunknown({i_data0,i_data1}) && ! $changed({i_data0,i_data1})) |-> ! $changed(o_data0) );

  // Identity cases (helpful for debug and formal strengthening)
  a_id0: assert property ( (! $isunknown(i_data0) && (i_data1 == '0)) |-> (o_data0 == i_data0) );
  a_id1: assert property ( (! $isunknown(i_data1) && (i_data0 == '0)) |-> (o_data0 == i_data1) );

  // Coverage: key functional corners
  c_zero_zero:     cover property ( (i_data0 == '0) && (i_data1 == '0) );
  c_id0_cov:       cover property ( (i_data1 == '0) && (i_data0 != '0) );
  c_id1_cov:       cover property ( (i_data0 == '0) && (i_data1 != '0) );
  c_wrap:          cover property ( ! $isunknown({i_data0,i_data1}) && ((i_data0 + i_data1) < i_data0) ); // unsigned wrap
  c_no_wrap:       cover property ( ! $isunknown({i_data0,i_data1}) && ((i_data0 + i_data1) >= i_data0) );
  c_max_plus_one:  cover property ( (i_data0 == '1) && (i_data1 == {{(WIDTH-1){1'b0}},1'b1}) );
  c_cancel_to_zero:cover property ( ! $isunknown({i_data0,i_data1}) && ((i_data0 + i_data1) == '0) && ((i_data0 != '0) || (i_data1 != '0)) );

endmodule

// Bind into DUT
bind adder_block adder_block_sva #(.WIDTH(32))
  u_adder_block_sva (.i_data0(i_data0), .i_data1(i_data1), .o_data0(o_data0));