module gray_code_state_machine_sva (
    input logic clk,
    input logic gray_code,
    input logic out,
    input logic rst,
    input logic state,
    input logic data_15,
    input logic data_16,
    input logic data_17,
    input logic data_18,
    input logic data_19,
    input logic data_20,
    input logic data_21,
    input logic data_22,
    input logic data_23,
    input logic data_24,
    input logic data_25,
    input logic data_26,
    input logic data_27,
    input logic data_28,
    input logic data_29,
    input logic data_30,
    input logic data_31
);

property ResetSynceotid; @(posedge clk) (rst) |-> state == 0 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(posedge clk) (rst) |-> gray_code == 0 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(posedge clk) (rst) |-> out == 0 ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(posedge clk) !rst |-> state == gray_code ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(posedge clk) !rst |-> gray_code == 0 ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(posedge clk) !rst |-> out == 0 ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(posedge clk) (rst) |-> data_15 == 0 ;endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(posedge clk) (rst) |-> data_16 == 0 ;endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(posedge clk) (rst) |-> data_17 == 0 ;endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(posedge clk) (rst) |-> data_18 == 0 ;endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(posedge clk) (rst) |-> data_19 == 0 ;endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(posedge clk) (rst) |-> data_20 == 0 ;endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(posedge clk) (rst) |-> data_21 == 0 ;endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(posedge clk) (rst) |-> data_22 == 0 ;endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(posedge clk) (rst) |-> data_23 == 0 ;endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(posedge clk) (rst) |-> data_24 == 0 ;endproperty
assert property (ResetSynceotid_16);

property ResetSynceotid_17; @(posedge clk) (rst) |-> data_25 == 0 ;endproperty
assert property (ResetSynceotid_17);

property ResetSynceotid_18; @(posedge clk) (rst) |-> data_26 == 0 ;endproperty
assert property (ResetSynceotid_18);

property ResetSynceotid_19; @(posedge clk) (rst) |-> data_27 == 0 ;endproperty
assert property (ResetSynceotid_19);

property ResetSynceotid_20; @(posedge clk) (rst) |-> data_28 == 0 ;endproperty
assert property (ResetSynceotid_20);

property ResetSynceotid_21; @(posedge clk) (rst) |-> data_29 == 0 ;endproperty
assert property (ResetSynceotid_21);

property ResetSynceotid_22; @(posedge clk) (rst) |-> data_30 == 0 ;endproperty
assert property (ResetSynceotid_22);

property ResetSynceotid_23; @(posedge clk) (rst) |-> data_31 == 0 ;endproperty
assert property (ResetSynceotid_23);

endmodule