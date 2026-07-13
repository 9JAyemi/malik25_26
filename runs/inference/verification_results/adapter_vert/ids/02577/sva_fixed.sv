module mux_4_to_1_sva (
    input logic d0,
    input logic d1,
    input logic d2,
    input logic d3,
    input logic out,
    input logic sel1,
    input logic sel2,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (sel1) && (sel2) |-> (out) == (d3) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (sel1) && (!sel2) |-> (out) == (d2) ; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (!sel1) && (sel2) |-> (out) == (d1) ; endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (!sel1) && (!sel2) |-> (out) == (d0) ; endproperty
assert property (ValidDataeotid_4);

endmodule