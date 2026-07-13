module top_module_sva (
    input logic in1,
    input logic in2,
    input logic max_out,
    input logic out,
    input logic sum,
    input logic clk_in_11
);

property SyncAddereotid; @(posedge clk_in_11) ( in1 ) + ( in2 ) == ( sum ) ; endproperty
assert property (SyncAddereotid);

property MaxSynceotid; @(posedge clk_in_11) ( out ) == ( sum ) ; endproperty
assert property (MaxSynceotid);

property MaxSynceotid_2; @(posedge clk_in_11) ( max_out ) == (  ( out ) > ( sum )  ? ( out ) : ( sum )  ) ; endproperty
assert property (MaxSynceotid_2);

endmodule