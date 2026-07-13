module parity_checker_sva (
    input logic data_in,
    input logic parity,
    input logic sel_b1,
    input logic xor_out,
    input logic clk_in_1
);

property DataSynceotid; @(posedge clk_in_1) (sel_b1) |-> (parity) == (~xor_out) ; endproperty
assert property (DataSynceotid);

property SyncCheckeotid; @(posedge clk_in_1) (sel_b1) |-> (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) ; endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_1) ! (sel_b1) |-> (parity) == (xor_out) ; endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_1) ! (sel_b1) |-> (data_in[0] ^ data_in[1] ^ data_in[2] ^ data_in[3] ^ data_in[4] ^ data_in[5] ^ data_in[6] ^ data_in[7]) ; endproperty
assert property (SyncCheckeotid_3);

endmodule