module bitwise_and_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic clk_in_17
);

property BitwiseAndeotid; @(posedge clk_in_17) (A) & (B) |-> (C) ;endproperty
assert property (BitwiseAndeotid);

property SyncIneotid; @(posedge clk_in_17) (A) & (B) |-> (C) ;endproperty
assert property (SyncIneotid);

property SyncIneotid_2; @(posedge clk_in_17) (A) & (B) |-> (C) ;endproperty
assert property (SyncIneotid_2);

endmodule