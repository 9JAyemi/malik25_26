module multi_input_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic A4,
    input logic B1,
    input logic X,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (A1) && (A2) && (A3) |-> (X) ; endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_14) (A1) && (A2) && (A4) |-> (X) ; endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_14) (A1) && (A3) && (A4) |-> (X) ; endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_14) (A2) && (A3) && (A4) |-> (X) ; endproperty
assert property (SyncIneotid_4);

property SyncIneotid_5; @(posedge clk_in_14) (A1) && (A2) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_5);

property SyncIneotid_6; @(posedge clk_in_14) (A1) && (A3) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_6);

property SyncIneotid_7; @(posedge clk_in_14) (A1) && (A4) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_7);

property SyncIneotid_8; @(posedge clk_in_14) (A2) && (A3) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_8);

property SyncIneotid_9; @(posedge clk_in_14) (A2) && (A4) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_9);

property SyncIneotid_10; @(posedge clk_in_14) (A3) && (A4) &&  (B1)  |-> (X) ; endproperty
assert property (SyncIneotid_10);

endmodule