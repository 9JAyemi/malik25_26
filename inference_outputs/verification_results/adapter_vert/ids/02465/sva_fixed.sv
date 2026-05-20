module my_module_sva (
    input logic A1,
    input logic A2,
    input logic A3,
    input logic B1,
    input logic X,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1) |-> X == 1'b1 ;endproperty
assert property (ClockSynceotid);

property SyncCheckeotid; @(posedge clk_in_1) (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1) && (  (A1 & ~A2) | (A2 & ~A1 & A3 & ~B1) | (~A1 & ~A2 & ~A3 & B1)  != 1'b1  ) |-> X == 1'b0 ;endproperty
assert property (SyncCheckeotid);

endmodule