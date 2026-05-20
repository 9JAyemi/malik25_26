module mux_adder_sva (
    input logic data0_mux1,
    input logic data0_mux2,
    input logic data1_mux1,
    input logic data1_mux2,
    input logic data2_mux1,
    input logic data2_mux2,
    input logic data3_mux1,
    input logic data3_mux2,
    input logic data4_mux1,
    input logic data4_mux2,
    input logic data5_mux1,
    input logic data5_mux2,
    input logic mux1_out,
    input logic mux2_out,
    input logic mux_sel,
    input logic out,
    input logic sel_mux,
    input logic sel_mux1,
    input logic sel_mux2,
    input logic b0,
    input logic b000,
    input logic b0000,
    input logic b001,
    input logic b010,
    input logic b011,
    input logic b100,
    input logic b101,
    input logic clk_in_1
);

property DataSynceotid; @(posedge clk_in_1) (sel_mux1) == (3'b000) |-> (mux1_out) == (data0_mux1) ; endproperty
assert property (DataSynceotid);

property DataSynceotid_2; @(posedge clk_in_1) (sel_mux1) == (3'b001) |-> (mux1_out) == (data1_mux1) ; endproperty
assert property (DataSynceotid_2);

property DataSynceotid_3; @(posedge clk_in_1) (sel_mux1) == (3'b010) |-> (mux1_out) == (data2_mux1) ; endproperty
assert property (DataSynceotid_3);

property DataSynceotid_4; @(posedge clk_in_1) (sel_mux1) == (3'b011) |-> (mux1_out) == (data3_mux1) ; endproperty
assert property (DataSynceotid_4);

property DataSynceotid_5; @(posedge clk_in_1) (sel_mux1) == (3'b100) |-> (mux1_out) == (data4_mux1) ; endproperty
assert property (DataSynceotid_5);

property DataSynceotid_6; @(posedge clk_in_1) (sel_mux1) == (3'b101) |-> (mux1_out) == (data5_mux1) ; endproperty
assert property (DataSynceotid_6);

property SyncDataeotid; @(posedge clk_in_1) (sel_mux1) != 3'b000 && (sel_mux1) != 3'b001 && (sel_mux1) != 3'b010 && (sel_mux1) != 3'b011 && (sel_mux1) != 3'b100 && (sel_mux1) != 3'b101  |-> (mux1_out) == 4'b0000; endproperty
assert property (SyncDataeotid);

property DataSynceotid_7; @(posedge clk_in_1) (sel_mux2) == (3'b000) |-> (mux2_out) == (data0_mux2) ; endproperty
assert property (DataSynceotid_7);

property DataSynceotid_8; @(posedge clk_in_1) (sel_mux2) == (3'b001) |-> (mux2_out) == (data1_mux2) ; endproperty
assert property (DataSynceotid_8);

property DataSynceotid_9; @(posedge clk_in_1) (sel_mux2) == (3'b010) |-> (mux2_out) == (data2_mux2) ; endproperty
assert property (DataSynceotid_9);

property DataSynceotid_10; @(posedge clk_in_1) (sel_mux2) == (3'b011) |-> (mux2_out) == (data3_mux2) ; endproperty
assert property (DataSynceotid_10);

property DataSynceotid_11; @(posedge clk_in_1) (sel_mux2) == (3'b100) |-> (mux2_out) == (data4_mux2) ; endproperty
assert property (DataSynceotid_11);

property DataSynceotid_12; @(posedge clk_in_1) (sel_mux2) == (3'b101) |-> (mux2_out) == (data5_mux2) ; endproperty
assert property (DataSynceotid_12);

property SyncDataeotid_2; @(posedge clk_in_1) (sel_mux2) != 3'b000 && (sel_mux2) != 3'b001 && (sel_mux2) != 3'b010 && (sel_mux2) != 3'b011 && (sel_mux2) != 3'b100 && (sel_mux2) != 3'b101  |-> (mux2_out) == 4'b0000; endproperty
assert property (SyncDataeotid_2);

property SyncAddereotid; @(posedge clk_in_1) (mux1_out) and @(posedge clk_in_1) (mux2_out) |-> (out) == (mux1_out + mux2_out) ; endproperty
assert property (SyncAddereotid);

property SyncCheckeotid; @(posedge clk_in_1) (sel_mux) == (1'b0) |-> (mux_sel) == (sel_mux1) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) (sel_mux) != 1'b0  |-> (mux_sel) == (sel_mux2) ; endproperty
assert property (SyncCheckeotid_2);

endmodule