module Mux4_1_sva (
    input logic Data_in,
    input logic Data_out,
    input logic clk_in_1
);

property DataSynceotid; @(posedge clk_in_1) (Data_in) |-> (Data_out) ;endproperty
assert property (DataSynceotid);

endmodule