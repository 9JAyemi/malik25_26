module and4b_sva (
    input logic A_N,
    input logic B,
    input logic C,
    input logic D,
    input logic X,
    input logic clk_in_14
);

property SyncIneotid; @(posedge clk_in_14) (A_N) |->  (X) == ( ~ (A_N | B | C | D) );endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_14) (B) |->  (X) == ( ~ (A_N | B | C | D) );endproperty
assert property (SyncIneotid_2);

property SyncIneotid_3; @(posedge clk_in_14) (C) |->  (X) == ( ~ (A_N | B | C | D) );endproperty
assert property (SyncIneotid_3);

property SyncIneotid_4; @(posedge clk_in_14) (D) |->  (X) == ( ~ (A_N | B | C | D) );endproperty
assert property (SyncIneotid_4);

endmodule