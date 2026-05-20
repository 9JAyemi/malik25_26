module bin2gray_sva (
    input logic bin,
    input logic gray,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (bin) |-> (gray) ;endproperty
assert property (ClockSynceotid);

property GraySynceotid; @(posedge clk_in_1) (bin) |-> (gray) ;endproperty
assert property (GraySynceotid);

property GraySynceotid_2; @(posedge clk_in_1) (bin) |-> (gray) ;endproperty
assert property (GraySynceotid_2);

property GraySynceotid_3; @(posedge clk_in_1) (bin) |-> (gray) ;endproperty
assert property (GraySynceotid_3);

endmodule