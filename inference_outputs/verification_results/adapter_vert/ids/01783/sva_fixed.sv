module two_bit_adder_sva (
    input logic A1_N,
    input logic A2_N,
    input logic B1,
    input logic B2,
    input logic X,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N); endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_14) (B1) != (B2); endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_14) (A1_N) != (B2); endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_14) (A2_N) != (B1); endproperty
assert property (SyncIneotid_4);

property SyncCheckeotid; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (B1) != (B2); endproperty
assert property (SyncCheckeotid);

property SyncCheckeotid_2; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (A1_N) != (B2); endproperty
assert property (SyncCheckeotid_2);

property SyncCheckeotid_3; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (A2_N) != (B1); endproperty
assert property (SyncCheckeotid_3);

property SyncCheckeotid_4; @(posedge clk_in_14) (X) != (A1_N) && (A2_N) && (B1) != (B2) && (A1_N) != (B2) && (A2_N) != (B1); endproperty
assert property (SyncCheckeotid_4);

endmodule