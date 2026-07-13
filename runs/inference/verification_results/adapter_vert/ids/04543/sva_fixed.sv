module my_nand2b_sva (
    input logic A_N,
    input logic B,
    input logic Y,
    input logic and0_out,
    input logic not0_out,
    input logic not1_out,
    input logic clk_in_17
);

property SyncIneotid; @(posedge clk_in_17) (B) |-> (not0_out) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_17) (A_N) |-> (not1_out) ;endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_17) (B) &&  (A_N) |-> (and0_out) ;endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_17) (B) &&  (A_N) |-> (Y) ;endproperty
assert property (SyncIneotid_4);

endmodule