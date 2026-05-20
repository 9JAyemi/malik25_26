module arithmetic_logic_unit_sva (
    input logic addresult,
    input logic aluc,
    input logic result,
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
    input logic b1100,
    input logic b1101,
    input logic b1110,
    input logic b1111,
    input logic clk_in_1
);

property ValidDataeotid; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid);

property ValidDataeotid_2; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_2);

property ValidDataeotid_3; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_3);

property ValidDataeotid_4; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_4);

property ValidDataeotid_5; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_5);

property ValidDataeotid_6; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_6);

property ValidDataeotid_7; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_7);

property ValidDataeotid_8; @(posedge clk_in_1) (aluc) == (4'b0001) | (aluc) == (4'b1001) |  (aluc) == (4'b0101) | (aluc) == (4'b1101)  |  (aluc) == (4'b1010) | (aluc) == (4'b0010) |  (aluc) == (4'b0110) | (aluc) == (4'b1110)  |  (aluc) == (4'b0000) | (aluc) == (4'b1000) |  (aluc) == (4'b0100) | (aluc) == (4'b1100)  |  (aluc) == (4'b0011) | (aluc) == (4'b0111) |  (aluc) == (4'b1111)  |  (result) == (addresult) ;endproperty
assert property (ValidDataeotid_8);

endmodule