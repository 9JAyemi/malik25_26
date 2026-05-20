module power_good_sva (
    input logic and0_out,
    input logic and1_out,
    input logic and2_out,
    input logic and3_out,
    input logic and4_out,
    input logic and5_out,
    input logic and6_out,
    input logic and7_out,
    input logic in1,
    input logic in2,
    input logic in3,
    input logic in4,
    input logic in5,
    input logic in6,
    input logic in7,
    input logic in8,
    input logic in9,
    input logic out1,
    input logic clk_in_1
);

property ClockSynceotid; @(posedge clk_in_1) (and0_out) == (in1) && (in2) ; endproperty
assert property (ClockSynceotid);

property ValidSynceotid; @(posedge clk_in_1) (and1_out) == (in3) && (in4) ; endproperty
assert property (ValidSynceotid);

property ValidSynceotid_2; @(posedge clk_in_1) (and2_out) == (in5) && (in6) ; endproperty
assert property (ValidSynceotid_2);

property ValidSynceotid_3; @(posedge clk_in_1) (and3_out) == (in7) && (in8) ; endproperty
assert property (ValidSynceotid_3);

property ValidSynceotid_4; @(posedge clk_in_1) (and4_out) == (and0_out) && (and1_out) ; endproperty
assert property (ValidSynceotid_4);

property ValidSynceotid_5; @(posedge clk_in_1) (and5_out) == (and2_out) && (and3_out) ; endproperty
assert property (ValidSynceotid_5);

property ValidSynceotid_6; @(posedge clk_in_1) (and6_out) == (and4_out) && (and5_out) ; endproperty
assert property (ValidSynceotid_6);

property ValidSynceotid_7; @(posedge clk_in_1) (and7_out) == (and6_out) && (in9) ; endproperty
assert property (ValidSynceotid_7);

property ValidOuteotid; @(posedge clk_in_1) (out1) == (and7_out) ; endproperty
assert property (ValidOuteotid);

endmodule