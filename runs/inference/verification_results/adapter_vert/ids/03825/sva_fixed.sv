module binary_adder_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic CTRL,
    input logic b0,
    input logic clk_in_13
);

property SyncAdderCheckeotid; @(posedge clk_in_13) (CTRL) == (0) |-> (C) == (A + B) ; endproperty
assert property (SyncAdderCheckeotid);

property SyncAddereotid; @(posedge clk_in_13) (CTRL) != 0 |-> (C) == ({1'b0, A[3:1]} + {1'b0, B[3:1]}); endproperty
assert property (SyncAddereotid);

endmodule