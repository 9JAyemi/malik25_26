module top_module_sva (
    input logic a,
    input logic adder_output,
    input logic b,
    input logic clk,
    input logic comparator_output,
    input logic ctrl,
    input logic mux_output,
    input logic b0,
    input logic b001,
    input logic b010,
    input logic b100
);

property AddOneeotid; @(posedge clk) (a) + (b) == (adder_output) ; endproperty
assert property (AddOneeotid);

property Compareeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) > (b) |-> (comparator_output) == 3'b100 ; endproperty
assert property (Compareeotid);

property SyncEqeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) != (b)  |-> (comparator_output) == 3'b001 ; endproperty
assert property (SyncEqeotid);

property yncEqeotid; @(posedge clk) (a) + (b) == (adder_output) && (a) == (b) |-> (comparator_output) == 3'b010 ; endproperty
assert property (yncEqeotid);

property SyncCheckeotid; @(posedge clk) (ctrl) ?  (mux_output) ==  {1'b0, (comparator_output)}  :  (mux_output) ==  (adder_output) ; endproperty
assert property (SyncCheckeotid);

endmodule