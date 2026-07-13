module rominfr_sva (
    input logic addr,
    input logic clk,
    input logic data,
    input logic en,
    input logic b0000,
    input logic b00001,
    input logic b00010,
    input logic b00011,
    input logic b0010,
    input logic b00100,
    input logic b00101,
    input logic b00110,
    input logic b00111,
    input logic b0100,
    input logic b01000,
    input logic b01001,
    input logic b01010,
    input logic b01011,
    input logic b01100,
    input logic b01101,
    input logic b01110,
    input logic b01111,
    input logic b1010,
    input logic b1100,
    input logic b1110,
    input logic bXXXX
);

property ClockSynceotid; @(posedge clk) (en) |-> data == 4'b0010 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk) (en) && ( addr == 5'b00001 ) |-> data == 4'b0010 ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk) (en) && ( addr == 5'b00010 ) |-> data == 4'b1110 ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk) (en) && ( addr == 5'b00011 ) |-> data == 4'b0010 ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk) (en) && ( addr == 5'b00100 ) |-> data == 4'b0100 ; endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk) (en) && ( addr == 5'b00101 ) |-> data == 4'b1010 ; endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk) (en) && ( addr == 5'b00110 ) |-> data == 4'b1100 ; endproperty
assert property (ClockSynceotid_7);

property ClockSynceotid_8; @(posedge clk) (en) && ( addr == 5'b00111 ) |-> data == 4'b0000 ; endproperty
assert property (ClockSynceotid_8);

property ClockSynceotid_9; @(posedge clk) (en) && ( addr == 5'b01000 ) |-> data == 4'b1010 ; endproperty
assert property (ClockSynceotid_9);

property ClockSynceotid_10; @(posedge clk) (en) && ( addr == 5'b01001 ) |-> data == 4'b0010 ; endproperty
assert property (ClockSynceotid_10);

property ClockSynceotid_11; @(posedge clk) (en) && ( addr == 5'b01010 ) |-> data == 4'b1110 ; endproperty
assert property (ClockSynceotid_11);

property ClockSynceotid_12; @(posedge clk) (en) && ( addr == 5'b01011 ) |-> data == 4'b0010 ; endproperty
assert property (ClockSynceotid_12);

property ClockSynceotid_13; @(posedge clk) (en) && ( addr == 5'b01100 ) |-> data == 4'b0100 ; endproperty
assert property (ClockSynceotid_13);

property ClockSynceotid_14; @(posedge clk) (en) && ( addr == 5'b01101 ) |-> data == 4'b1010 ; endproperty
assert property (ClockSynceotid_14);

property ClockSynceotid_15; @(posedge clk) (en) && ( addr == 5'b01110 ) |-> data == 4'b1100 ; endproperty
assert property (ClockSynceotid_15);

property ClockSynceotid_16; @(posedge clk) (en) && ( addr == 5'b01111 ) |-> data == 4'b0000 ; endproperty
assert property (ClockSynceotid_16);

property SafeAccesseotid; @(posedge clk) ! (en)  |-> data == 4'bXXXX ; endproperty
assert property (SafeAccesseotid);

endmodule