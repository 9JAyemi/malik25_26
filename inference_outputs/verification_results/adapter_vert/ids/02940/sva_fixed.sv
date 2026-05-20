module add_sub_sva (
    input logic A,
    input logic B,
    input logic clk,
    input logic operation,
    input logic reset,
    input logic result,
    input logic b0000
);

property ResetSynceotid; @(posedge clk) (reset) |-> result == 4'b0000 ;endproperty
assert property (ResetSynceotid);

property AddOnReseteotid; @(posedge clk) (reset) &&  (  operation == 0 ) |-> result == (A + B) ;endproperty
assert property (AddOnReseteotid);

property SubOnReseteotid; @(posedge clk) (reset) &&  (  operation != 0 ) |-> result == (A - B) ;endproperty
assert property (SubOnReseteotid);

endmodule