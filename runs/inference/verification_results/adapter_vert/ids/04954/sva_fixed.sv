module pipelined_adder_sva (
    input logic A,
    input logic B,
    input logic OUT,
    input logic clk,
    input logic sum_reg1,
    input logic sum_reg2,
    input logic sum_reg3
);

property SyncAdderCheckeotid; @(posedge clk) (A) + (B) == (sum_reg1) ;endproperty
assert property (SyncAdderCheckeotid);

property SyncAddereotid; @(posedge clk) (sum_reg1) == (sum_reg2) ;endproperty
assert property (SyncAddereotid);

property SyncCheckeotid; @(posedge clk) (sum_reg2) == (sum_reg3) ;endproperty
assert property (SyncCheckeotid);

property SyncAddereotid_2; @(posedge clk) (A) + (B) == (OUT) ;endproperty
assert property (SyncAddereotid_2);

endmodule