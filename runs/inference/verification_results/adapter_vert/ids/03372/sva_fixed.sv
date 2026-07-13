module mux4to1_sva (
    input logic in,
    input logic out,
    input logic sel,
    input logic b0000,
    input logic b000000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic clk_in_13
);

property ClockSynceotid; @(posedge clk_in_13) (sel) == (4'b0000) |-> (out) == (in) ; endproperty
assert property (ClockSynceotid);

property ValidDataeotid; @(posedge clk_in_13) (sel) == (4'b0001) |-> (out) == (in) ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_13) (sel) == (4'b0010) |-> (out) == (in) ; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_13) (sel) == (4'b0011) |-> (out) == (in) ; endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_13) (sel) != 4'b0000 && @(posedge clk_in_13) (sel) != 4'b0001 && @(posedge clk_in_13) (sel) != 4'b0010 && @(posedge clk_in_13) (sel) != 4'b0011  |-> (out) == 6'b000000; endproperty
assert property (ValidDataeotid_4);

endmodule