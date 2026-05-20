module comparator_sva (
    input logic A,
    input logic B,
    input logic EQ,
    input logic GT,
    input logic b1,
    input logic clk_in_1
);

property SyncEqeotid; @(posedge clk_in_1) ( A ) == (  B ) |-> ( EQ ) == 1'b1 ;endproperty
assert property (SyncEqeotid);

property SyncGtNoteThisnameis; @(posedge clk_in_1) ( A ) != (  B ) &&  (  A  -  B  )  |-> ( GT ) == 1'b1 ;endproperty
assert property (SyncGtNoteThisnameis);

endmodule