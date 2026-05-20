module multiplexer_sva (
    input logic a,
    input logic b,
    input logic c,
    input logic clk,
    input logic counter,
    input logic d,
    input logic flip_flops_out,
    input logic mux_out,
    input logic q,
    input logic reset,
    input logic b000,
    input logic b00000000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0110,
    input logic b1,
    input logic b1000,
    input logic b1100,
    input logic b111,
    input logic b1111
);

property ClockSynceotid; @(posedge clk) (a) |-> (mux_out) == 4'b0001 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (b) |-> (mux_out) == 4'b0010 ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (c) |-> (mux_out) == 4'b0100 ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (a) && (b) && (c) |-> (mux_out) == 4'b1000 ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (a) != (b) && (b) != (c) && (a) != (c)  |-> (mux_out) == 4'b0011 ; endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk) (a) != (b)  && (b) != (c) && (a) == (c)  |-> (mux_out) == 4'b0110 ; endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk) (a) != (b)  && (b) == (c) && (a) != (c)  |-> (mux_out) == 4'b1100 ; endproperty
assert property (ClockSynceotid_7);

property ClockSynceotid_8; @(posedge clk) (a) != (b)  && (b) == (c) && (a) == (c)  |-> (mux_out) == 4'b1111 ; endproperty
assert property (ClockSynceotid_8);

property ResetSynceotid; @(posedge clk) (reset) |-> (flip_flops_out) == 8'b00000000 && (counter) == 3'b000; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (reset) != 1'b1  && (counter) != 3'b111 |-> (flip_flops_out) == (d) && (counter) == 3'b000; endproperty
assert property (ResetSynceotid_2);

property SyncCtrleotid; @(posedge clk) (reset) != 1'b1  && (counter)  == 3'b111  |-> (flip_flops_out) == (d) && (counter) == 3'b000; endproperty
assert property (SyncCtrleotid);

property SyncCtrleotid_2; @(posedge clk) (reset) != 1'b1  && (counter) != 3'b111  |-> (counter) == (counter) + 1; endproperty
assert property (SyncCtrleotid_2);

property SyncFloweotid; @(posedge clk)  (  clk  &&  reset  &&  d  !=  q ) |->  (  q  ==  d  &&  counter  ==  3'b000 ) ; endproperty
assert property (SyncFloweotid);

endmodule