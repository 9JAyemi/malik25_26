// SVA for Multiplexer4
// Bind this module to the DUT and provide a simulation/formal clock.
// Example bind (replace clk with your env clock):
// bind Multiplexer4 Multiplexer4_sva #(.width(width)) u_mux4_sva (.* , .clk(clk));

module Multiplexer4_sva #(parameter int width = 3) (
  input logic                          clk,
  input logic [width-1:0]              i_data0,
  input logic [width-1:0]              i_data1,
  input logic [width-1:0]              i_data2,
  input logic [width-1:0]              i_data3,
  input logic                          i_select0,
  input logic                          i_select1,
  input logic                          i_select2,
  input logic                          i_select3,
  input logic [width-1:0]              o_data,
  input logic                          o_error
);

  default clocking cb @(posedge clk); endclocking

  logic [3:0] sel;
  assign sel = {i_select3, i_select2, i_select1, i_select0};

  function automatic bit valid_sel (logic [3:0] s);
    return (s inside {4'b0000,4'b0001,4'b0010,4'b0011});
  endfunction

  // Correct data routing and no error for valid selections
  assert property (sel == 4'b0000 |-> (o_data == i_data0 && !o_error));
  assert property (sel == 4'b0001 |-> (o_data == i_data1 && !o_error));
  assert property (sel == 4'b0010 |-> (o_data == i_data2 && !o_error));
  assert property (sel == 4'b0011 |-> (o_data == i_data3 && !o_error));

  // Invalid selection must raise error and drive zero
  assert property (!valid_sel(sel) |-> (o_error && o_data == '0));

  // No spurious error in valid selections; error only if invalid
  assert property ( valid_sel(sel) |-> !o_error );
  assert property ( o_error |-> !valid_sel(sel) );

  // o_error should never be X/Z (catches latch/undriven issues)
  assert property ( !$isunknown(o_error) );

  // Optional X-propagation sanity: if selected input is known, output is known
  assert property ( (sel==4'b0000 && !$isunknown(i_data0)) |-> !$isunknown(o_data) );
  assert property ( (sel==4'b0001 && !$isunknown(i_data1)) |-> !$isunknown(o_data) );
  assert property ( (sel==4'b0010 && !$isunknown(i_data2)) |-> !$isunknown(o_data) );
  assert property ( (sel==4'b0011 && !$isunknown(i_data3)) |-> !$isunknown(o_data) );

  // Coverage: hit each valid selection and an invalid selection
  cover property (sel == 4'b0000 && o_data == i_data0 && !o_error);
  cover property (sel == 4'b0001 && o_data == i_data1 && !o_error);
  cover property (sel == 4'b0010 && o_data == i_data2 && !o_error);
  cover property (sel == 4'b0011 && o_data == i_data3 && !o_error);
  cover property (!valid_sel(sel) && o_error && o_data == '0);

  // Transition coverage across all valid codes
  cover property (sel == 4'b0000 ##1 sel == 4'b0001 ##1 sel == 4'b0010 ##1 sel == 4'b0011);

endmodule