module mm_sva (
    input logic addr,
    input logic eff_addr,
    input logic mod,
    input logic clk_in_1,
    input logic h0,
    input logic h00,
    input logic h000,
    input logic h1,
    input logic h10,
    input logic h2,
    input logic h3,
    input logic h4,
    input logic h5,
    input logic h6,
    input logic h7,
    input logic h8,
    input logic h9,
    input logic hb,
    input logic hf00,
    input logic hf01,
    input logic hf02,
    input logic hf03,
    input logic hf04,
    input logic hf05,
    input logic hf06,
    input logic hf07,
    input logic hf08,
    input logic hf0a
);

property ValidAddrCheckeotid; @(posedge clk_in_1) (addr) == (12'h000) |-> (mod) == 8'h0 ; endproperty
assert property (ValidAddrCheckeotid);

property ValidAddrRuneotid; @(posedge clk_in_1) (addr) == (8'h10) |-> (mod) == 8'h1 ; endproperty
assert property (ValidAddrRuneotid);

property ValidAddrRuneotid_2; @(posedge clk_in_1) (addr) == (12'hf00) |-> (mod) == 8'h2 ; endproperty
assert property (ValidAddrRuneotid_2);

property ValidAddrRuneotid_3; @(posedge clk_in_1) (addr) == (12'hf01) |-> (mod) == 8'h3 ; endproperty
assert property (ValidAddrRuneotid_3);

property ValidAddrRuneotid_4; @(posedge clk_in_1) (addr) == (12'hf02) |-> (mod) == 8'h4 ; endproperty
assert property (ValidAddrRuneotid_4);

property ValidAddrRuneotid_5; @(posedge clk_in_1) (addr) == (12'hf03) |-> (mod) == 8'h5 ; endproperty
assert property (ValidAddrRuneotid_5);

property ValidAddrRuneotid_6; @(posedge clk_in_1) (addr) == (12'hf04) |-> (mod) == 8'h6 ; endproperty
assert property (ValidAddrRuneotid_6);

property ValidAddrRuneotid_7; @(posedge clk_in_1) (addr) == (12'hf05) |-> (mod) == 8'h7 ; endproperty
assert property (ValidAddrRuneotid_7);

property ValidAddrRuneotid_8; @(posedge clk_in_1) (addr) == (12'hf06) |-> (mod) == 8'h8 ; endproperty
assert property (ValidAddrRuneotid_8);

property ValidAddrRuneotid_9; @(posedge clk_in_1) (addr) == (12'hf07) |-> (mod) == 10'h2 ; endproperty
assert property (ValidAddrRuneotid_9);

property ValidAddrRuneotid_10; @(posedge clk_in_1) (addr) == (12'hf08) |-> (mod) == 11'hb ; endproperty
assert property (ValidAddrRuneotid_10);

property ValidAddrRuneotid_11; @(posedge clk_in_1) (addr) == (12'hf0a) |-> (mod) == 9'h9 ; endproperty
assert property (ValidAddrRuneotid_11);

property ValidAddrRuneotid_12; @(posedge clk_in_1) (addr) != 12'h000 && @(posedge clk_in_1) (addr) != 8'h10 && @(posedge clk_in_1) (addr) != 12'hf00 && @(posedge clk_in_1) (addr) != 12'hf01 && @(posedge clk_in_1) (addr) != 12'hf02 && @(posedge clk_in_1) (addr) != 12'hf03 && @(posedge clk_in_1) (addr) != 12'hf04 && @(posedge clk_in_1) (addr) != 12'hf05 && @(posedge clk_in_1) (addr) != 12'hf06 && @(posedge clk_in_1) (addr) != 12'hf07 && @(posedge clk_in_1) (addr) != 12'hf08 && @(posedge clk_in_1) (addr) != 12'hf0a  |-> (mod) == 8'h0 ; endproperty
assert property (ValidAddrRuneotid_12);

property ValidAddrRuneotid_13; @(posedge clk_in_1) (mod) == 8'h1 |-> (eff_addr) == {8'h00,addr[23:0]} ; endproperty
assert property (ValidAddrRuneotid_13);

property ValidAddrRuneotid_14; @(posedge clk_in_1) (mod) != 8'h1  |-> (eff_addr) == {12'h000,addr[19:0]} ; endproperty
assert property (ValidAddrRuneotid_14);

endmodule