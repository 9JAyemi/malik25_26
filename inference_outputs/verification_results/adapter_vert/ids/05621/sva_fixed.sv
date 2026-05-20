module ClockDivider_sva (
    input logic Divisor,
    input logic clk,
    input logic clkOut_i,
    input logic count_i,
    input logic rst,
    input logic b0
);

property ResetSynceotid; @(posedge clk) (rst) |-> (count_i) == 0 ;endproperty
assert property (ResetSynceotid);

property ClockSynceotid; @(posedge clk) (rst) |-> (clkOut_i) == 0 ;endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (rst) &&  (  ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))  ) |-> (count_i) == 0 ;endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (rst) &&  (  ! (  ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))  )  ) |-> (count_i) == (count_i + 1) ;endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (rst) &&  (  ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))  ) |-> (clkOut_i) == (!clkOut_i) ;endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (rst) &&  (  ! (  ($signed({1'b0, count_i}) == ($signed({1'b0, Divisor}) - 1))  )  ) |-> (clkOut_i) == clkOut_i ;endproperty
assert property (ClockSynceotid_5);

endmodule