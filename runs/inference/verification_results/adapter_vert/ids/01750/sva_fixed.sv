module MUX16_sva (
    input logic data_i00,
    input logic data_i01,
    input logic data_i02,
    input logic data_i03,
    input logic data_i04,
    input logic data_i05,
    input logic data_i06,
    input logic data_i07,
    input logic data_i08,
    input logic data_i09,
    input logic data_i10,
    input logic data_i11,
    input logic data_i12,
    input logic data_i13,
    input logic data_i14,
    input logic data_i15,
    input logic data_o,
    input logic select,
    input logic b0000,
    input logic b0001,
    input logic b0010,
    input logic b0011,
    input logic b0100,
    input logic b0101,
    input logic b0110,
    input logic b0111,
    input logic b1000,
    input logic b1001,
    input logic b1010,
    input logic b1011,
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_15
);

property DataSynceotid; @(posedge clk_in_15) (select) == (4'b0000) |-> data_o == data_i00 ; endproperty
assert property (DataSynceotid);

property ValidDataeotid; @(posedge clk_in_15) (select) == (4'b0001) |-> data_o == data_i01 ; endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_15) (select) == (4'b0010) |-> data_o == data_i02 ; endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_15) (select) == (4'b0011) |-> data_o == data_i03 ; endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_15) (select) == (4'b0100) |-> data_o == data_i04 ; endproperty
assert property (ValidDataeotid_4);

property ValidDataeotid_5; @(posedge clk_in_15) (select) == (4'b0101) |-> data_o == data_i05 ; endproperty
assert property (ValidDataeotid_5);

property ValidDataeotid_6; @(posedge clk_in_15) (select) == (4'b0110) |-> data_o == data_i06 ; endproperty
assert property (ValidDataeotid_6);

property ValidDataeotid_7; @(posedge clk_in_15) (select) == (4'b0111) |-> data_o == data_i07 ; endproperty
assert property (ValidDataeotid_7);

property ValidDataeotid_8; @(posedge clk_in_15) (select) == (4'b1000) |-> data_o == data_i08 ; endproperty
assert property (ValidDataeotid_8);

property ValidDataeotid_9; @(posedge clk_in_15) (select) == (4'b1001) |-> data_o == data_i09 ; endproperty
assert property (ValidDataeotid_9);

property ValidDataeotid_10; @(posedge clk_in_15) (select) == (4'b1010) |-> data_o == data_i10 ; endproperty
assert property (ValidDataeotid_10);

property ValidDataeotid_11; @(posedge clk_in_15) (select) == (4'b1011) |-> data_o == data_i11 ; endproperty
assert property (ValidDataeotid_11);

property ValidDataeotid_12; @(posedge clk_in_15) (select) == (4'b1100) |-> data_o == data_i12 ; endproperty
assert property (ValidDataeotid_12);

property ValidDataeotid_13; @(posedge clk_in_15) (select) == (4'b1101) |-> data_o == data_i13 ; endproperty
assert property (ValidDataeotid_13);

property ValidDataeotid_14; @(posedge clk_in_15) (select) == (4'b1110) |-> data_o == data_i14 ; endproperty
assert property (ValidDataeotid_14);

property ValidDataeotid_15; @(posedge clk_in_15) (select) == (4'b1111) |-> data_o == data_i15 ; endproperty
assert property (ValidDataeotid_15);

endmodule