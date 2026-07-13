module udp_mux_4to1_sva (
    input logic in0,
    input logic in1,
    input logic out,
    input logic sel,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (sel) == (1'b0) |-> (out) == (in0); endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (sel) == (1'b1) |-> (out) == (in1); endproperty
assert property (ValidDataeotid_2);

endmodule