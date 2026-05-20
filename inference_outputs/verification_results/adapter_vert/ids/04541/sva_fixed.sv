module twos_complement_sva (
    input logic A,
    input logic Y,
    input logic invert,
    input logic b1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (invert) |-> (Y) == ( ~ (  ~ ( A )  + 1'b1 ) ); endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_1) (invert) &&  (  ~ (  ~ ( A )  + 1'b1 )  !=  (  ~ ( A )  + 1'b1 ) ) |-> (Y) != (  ~ ( A )  + 1'b1 ); endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_1) (  ~ (  ~ ( A )  + 1'b1 )  &&  (  ~ (  ~ ( A )  + 1'b1 )  !=  (  ~ ( A )  + 1'b1 )  ) ) |-> (Y) == (  ~ ( A )  + 1'b1 ); endproperty
assert property (ClockSynceotid_3);

endmodule