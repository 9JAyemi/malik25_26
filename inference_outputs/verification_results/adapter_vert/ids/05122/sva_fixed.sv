module splitter_sva (
    input logic in,
    input logic out1,
    input logic out2,
    input logic and_gate_15,
    input logic clk_in_1,
    input logic out
);

property SplitIneotid; @(posedge clk_in_1) (in) |-> (out1) == (in[7:0]); endproperty
assert property (SplitIneotid);

property SplitSynceotid; @(posedge clk_in_1) (in) |-> (out2) == (in[15:8]); endproperty
assert property (SplitSynceotid);

property ValidIneotid; @(posedge clk_in_1) (out2) &&  ( 0 ) |-> (out) == (and_gate_15); endproperty
assert property (ValidIneotid);

endmodule