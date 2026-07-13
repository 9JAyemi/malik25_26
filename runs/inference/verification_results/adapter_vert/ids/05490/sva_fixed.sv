module full_adder_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic b0,
    input logic b1,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (a) == (1'b0) && (b) == (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b0); endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (a) == (1'b0) && (b) == (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty
assert property (AddOneeotid_2);

property CarryOn; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty
assert property (CarryOn);

property CarryOneeotid; @(posedge clk_in_1) (a) != (1'b0) && (b) == (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b1); endproperty
assert property (CarryOneeotid);

property CarryOneeotid_2; @(posedge clk_in_1) (a) == (1'b0) && (b) != (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b1); endproperty
assert property (CarryOneeotid_2);

property CarryOneeotid_3; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) == (1'b0) |-> (sum) == (1'b0); endproperty
assert property (CarryOneeotid_3);

property AddOneeotid_3; @(posedge clk_in_1) (a) != (1'b0) && (b) == (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b0); endproperty
assert property (AddOneeotid_3);

property CarryOneeotid_4; @(posedge clk_in_1) (a) == (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b0); endproperty
assert property (CarryOneeotid_4);

property CarryOneeotid_5; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) |-> (sum) == (1'b1); endproperty
assert property (CarryOneeotid_5);

property AddOneeotid_4; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum) != (1'b1)  |->  (cout) ; endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  == (1'b1)  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_6);

property AddOneeotid_7; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_7);

property AddOneeotid_8; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_8);

property AddOneeotid_9; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_9);

property AddOneeotid_10; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_10);

property AddOneeotid_11; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_11);

property AddOneeotid_12; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_12);

property AddOneeotid_13; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_13);

property AddOneeotid_14; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_14);

property AddOneeotid_15; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_15);

property AddOneeotid_16; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_16);

property AddOneeotid_17; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_17);

property AddOneeotid_18; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_18);

property AddOneeotid_19; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_19);

property AddOneeotid_20; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_20);

property AddOneeotid_21; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) ; endproperty
assert property (AddOneeotid_21);

property AddOneeotid_22; @(posedge clk_in_1) (a) != (1'b0) && (b) != (1'b0) && (cin) != (1'b0) &&  (sum)  != (1'b1)  &&  (cout)  != 1'b0  |->  (cout) != 1'b0 ; endproperty
assert property (AddOneeotid_22);

endmodule