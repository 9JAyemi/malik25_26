module mux_2to1_sva (
    input logic data0,
    input logic data1,
    input logic data2,
    input logic data3,
    input logic out,
    input logic sel,
    input logic b1,
    input logic clk_in_1
);

property DataSynceotid; @(posedge clk_in_1) (sel) |-> (out) == (data1) ; endproperty
assert property (DataSynceotid);

property DataSynceotid_2; @(posedge clk_in_1) (sel) != 1'b1  |-> (out) == (data0) ; endproperty
assert property (DataSynceotid_2);

property DataSynceotid_3; @(posedge clk_in_1) (sel) &&  (data2)  &&  (data3)  |-> (out) == (data3) ; endproperty
assert property (DataSynceotid_3);

property DataSynceotid_4; @(posedge clk_in_1) (sel) &&  (data2)  &&  !(data3)  |-> (out) == (data2) ; endproperty
assert property (DataSynceotid_4);

endmodule