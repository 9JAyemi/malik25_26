module binary_counter_sva (
    input logic in,
    input logic out,
    input logic b00,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b01,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b10,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b11,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (in) == (4'b0000) |-> (out) == 2'b00 ; endproperty
assert property (ClockSynceotid);

property SyncOneotid; @(posedge clk_in_1) (in) == (4'b0001) |-> (out) == 2'b01 ; endproperty
assert property (SyncOneotid);

property SyncOneotid_2; @(posedge clk_in_1) (in) == (4'b0010) |-> (out) == 2'b01 ; endproperty
assert property (SyncOneotid_2);

property SyncOneotid_3; @(posedge clk_in_1) (in) == (4'b0011) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_3);

property SyncOneotid_4; @(posedge clk_in_1) (in) == (4'b0100) |-> (out) == 2'b01 ; endproperty
assert property (SyncOneotid_4);

property SyncOneotid_5; @(posedge clk_in_1) (in) == (4'b0101) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_5);

property SyncOneotid_6; @(posedge clk_in_1) (in) == (4'b0110) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_6);

property SyncOneotid_7; @(posedge clk_in_1) (in) == (4'b0111) |-> (out) == 2'b11 ; endproperty
assert property (SyncOneotid_7);

property SyncOneotid_8; @(posedge clk_in_1) (in) == (4'b1000) |-> (out) == 2'b01 ; endproperty
assert property (SyncOneotid_8);

property SyncOneotid_9; @(posedge clk_in_1) (in) == (4'b1001) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_9);

property SyncOneotid_10; @(posedge clk_in_1) (in) == (4'b1010) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_10);

property SyncOneotid_11; @(posedge clk_in_1) (in) == (4'b1011) |-> (out) == 2'b11 ; endproperty
assert property (SyncOneotid_11);

property SyncOneotid_12; @(posedge clk_in_1) (in) == (4'b1100) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_12);

property SyncOneotid_13; @(posedge clk_in_1) (in) == (4'b1101) |-> (out) == 2'b11 ; endproperty
assert property (SyncOneotid_13);

property SyncOneotid_14; @(posedge clk_in_1) (in) == (4'b1110) |-> (out) == 2'b11 ; endproperty
assert property (SyncOneotid_14);

property SyncOneotid_15; @(posedge clk_in_1) (in) == (4'b1111) |-> (out) == 2'b10 ; endproperty
assert property (SyncOneotid_15);

endmodule