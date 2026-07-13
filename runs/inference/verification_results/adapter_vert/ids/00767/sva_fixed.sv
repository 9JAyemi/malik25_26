module Video_System_CPU_nios2_oci_td_mode_sva (
    input logic ctrl,
    input logic td_mode,
    input logic b0000,
    input logic b0000000,
    input logic b0000001,
    input logic b0000010,
    input logic b0000011,
    input logic b0000100,
    input logic b0000101,
    input logic b0000110,
    input logic b0000111,
    input logic b0010,
    input logic b0100,
    input logic b0101,
    input logic b1000,
    input logic b1010,
    input logic b1100,
    input logic b1111,
    input logic clk_in_14
);

property ClockSynceotid; @(posedge clk_in_14) (ctrl) == (7'b0000000) |-> (td_mode) == 4'b0000 ; endproperty
assert property (ClockSynceotid);

property ClockSynceotid_2; @(posedge clk_in_14) (ctrl) == (7'b0000001) |-> (td_mode) == 4'b1000 ; endproperty
assert property (ClockSynceotid_2);

property ClockSynceotid_3; @(posedge clk_in_14) (ctrl) == (7'b0000010) |-> (td_mode) == 4'b0100 ; endproperty
assert property (ClockSynceotid_3);

property ClockSynceotid_4; @(posedge clk_in_14) (ctrl) == (7'b0000011) |-> (td_mode) == 4'b1100 ; endproperty
assert property (ClockSynceotid_4);

property ClockSynceotid_5; @(posedge clk_in_14) (ctrl) == (7'b0000100) |-> (td_mode) == 4'b0010 ; endproperty
assert property (ClockSynceotid_5);

property ClockSynceotid_6; @(posedge clk_in_14) (ctrl) == (7'b0000101) |-> (td_mode) == 4'b1010 ; endproperty
assert property (ClockSynceotid_6);

property ClockSynceotid_7; @(posedge clk_in_14) (ctrl) == (7'b0000110) |-> (td_mode) == 4'b0101 ; endproperty
assert property (ClockSynceotid_7);

property ClockSynceotid_8; @(posedge clk_in_14) (ctrl) == (7'b0000111) |-> (td_mode) == 4'b1111 ; endproperty
assert property (ClockSynceotid_8);

property SyncCtrleotid; (ctrl) != 7'b0000000 && (ctrl) != 7'b0000001 && (ctrl) != 7'b0000010 && (ctrl) != 7'b0000011 && (ctrl) != 7'b0000100 && (ctrl) != 7'b0000101 && (ctrl) != 7'b0000110 && (ctrl) != 7'b0000111  |-> (td_mode) == 4'b0000; endproperty
assert property (SyncCtrleotid);

endmodule