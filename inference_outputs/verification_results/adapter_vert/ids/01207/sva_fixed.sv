module priority_encoder_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic clk,
    input logic d,
    input logic in,
    input logic mux_out,
    input logic out_and,
    input logic priority_out,
    input logic b00,
    input logic b01,
    input logic b10,
    input logic b11,
    input logic h0,
    input logic h1,
    input logic h2,
    input logic h3,
    input logic out_or,
    input logic out_xor
);

property ClockSynceotid; @(posedge clk) (a) && (a > b) && (a > c) && (a > d) |-> priority_out == 2'b00 ; endproperty
assert property (ClockSynceotid);

property HighPrioSynceotid; @(posedge clk) (b) && (b > a) && (b > c) && (b > d) |-> priority_out == 2'b01 ; endproperty
assert property (HighPrioSynceotid);

property HighPrioSynceotid_2; @(posedge clk) (c) && (c > a) && (c > b) && (c > d) |-> priority_out == 2'b10 ; endproperty
assert property (HighPrioSynceotid_2);

property HighPrioSynceotid_3; @(posedge clk) (d) && (d > a) && (d > b) && (d > c) |-> priority_out == 2'b11 ; endproperty
assert property (HighPrioSynceotid_3);

property ClockSynceotid_2; @(posedge clk) (a) && (a > b) && (a > c) && (a > d) |-> mux_out == 8'h0 ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (b) && (b > a) && (b > c) && (b > d) |-> mux_out == 8'h1 ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (c) && (c > a) && (c > b) && (c > d) |-> mux_out == 8'h2 ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (d) && (d > a) && (d > b) && (d > c) |-> mux_out == 8'h3 ; endproperty
assert property (ClockSynceotid_5);

property ValidDataeotid; @(posedge clk) (in) |-> (out_and) && (out_or) && (out_xor) ; endproperty
assert property (ValidDataeotid);

endmodule