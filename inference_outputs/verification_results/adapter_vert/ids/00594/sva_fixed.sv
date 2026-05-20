module top_module_sva (
    input logic a,
    input logic adder_out,
    input logic b,
    input logic mux_out,
    input logic select,
    input logic sum,
    input logic b0,
    input logic cfg_16,
    input logic clk_in_1
);

property AddSynceotid; @(posedge clk_in_1) (select) |-> (sum) == (adder_out); endproperty
assert property (AddSynceotid);

property ValidDataeotid; @(posedge clk_in_1) (select) &&  (  ! (  a  &&  b  &&  cfg_16 ) ) |-> (sum) == (mux_out); endproperty
assert property (ValidDataeotid);

property AdderSynceotid; @(posedge clk_in_1) (  a  &&  b  &&  cfg_16 ) |-> (sum) == (  a  +  b  +  1'b0 ); endproperty
assert property (AdderSynceotid);

endmodule