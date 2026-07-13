module adder4bit_sva (
    input logic a,
    input logic b,
    input logic cin,
    input logic cout,
    input logic sum,
    input logic temp_sum,
    input logic b0001,
    input logic b0010,
    input logic b0100,
    input logic b1000,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (a) |-> (temp_sum) ; endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (b) |-> (temp_sum) ; endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (cin) |-> (temp_sum) ; endproperty
assert property (AddOneeotid_3);

property AddOneeotid_4; @(posedge clk_in_1) (a) && (b) && (cin) |-> (cout) ; endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> ! (cout) ; endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> ! (cout) ; endproperty
assert property (AddOneeotid_6);

property AddOneeotid_7; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> ! (cout) ; endproperty
assert property (AddOneeotid_7);

property AddOneeotid_8; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_8);

property AddOneeotid_9; @(posedge clk_in_1) (a) && ! (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_9);

property AddOneeotid_10; @(posedge clk_in_1) ! (a) && (b) && ! (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_10);

property AddOneeotid_11; @(posedge clk_in_1) ! (a) && ! (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_11);

property AddOneeotid_12; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_12);

property AddOneeotid_13; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_13);

property AddOneeotid_14; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_14);

property AddOneeotid_15; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_15);

property AddOneeotid_16; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_16);

property AddOneeotid_17; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_17);

property AddOneeotid_18; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_18);

property AddOneeotid_19; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_19);

property AddOneeotid_20; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_20);

property AddOneeotid_21; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_21);

property AddOneeotid_22; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_22);

property AddOneeotid_23; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_23);

property AddOneeotid_24; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_24);

property AddOneeotid_25; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_25);

property AddOneeotid_26; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_26);

property AddOneeotid_27; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_27);

property AddOneeotid_28; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_28);

property AddOneeotid_29; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_29);

property AddOneeotid_30; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_30);

property AddOneeotid_31; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_31);

property AddOneeotid_32; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_32);

property AddOneeotid_33; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_33);

property AddOneeotid_34; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_34);

property AddOneeotid_35; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_35);

property AddOneeotid_36; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_36);

property AddOneeotid_37; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_37);

property AddOneeotid_38; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_38);

property AddOneeotid_39; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_39);

property AddOneeotid_40; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_40);

property AddOneeotid_41; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_41);

property AddOneeotid_42; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_42);

property AddOneeotid_43; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_43);

property AddOneeotid_44; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_44);

property AddOneeotid_45; @(posedge clk_in_1) (a) && (b) && ! (cin) |-> (sum) == 4'b0010 ; endproperty
assert property (AddOneeotid_45);

property AddOneeotid_46; @(posedge clk_in_1) (a) && ! (b) && (cin) |-> (sum) == 4'b0100 ; endproperty
assert property (AddOneeotid_46);

property AddOneeotid_47; @(posedge clk_in_1) ! (a) && (b) && (cin) |-> (sum) == 4'b1000 ; endproperty
assert property (AddOneeotid_47);

property AddOneeotid_48; @(posedge clk_in_1) (a) && (b) && (cin) |-> (sum) == 4'b0001 ; endproperty
assert property (AddOneeotid_48);

endmodule