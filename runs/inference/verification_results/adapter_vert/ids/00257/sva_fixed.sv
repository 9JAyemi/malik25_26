module ripple_carry_adder_sva (
    input logic A,
    input logic B,
    input logic CIN,
    input logic COUT,
    input logic SUM,
    input logic clk_in_1
);

property AddOneeotid; @(posedge clk_in_1) (A) |-> (SUM) ;endproperty
assert property (AddOneeotid);

property AddOneeotid_2; @(posedge clk_in_1) (B) |-> (SUM) ;endproperty
assert property (AddOneeotid_2);

property AddOneeotid_3; @(posedge clk_in_1) (CIN) |-> (SUM) ;endproperty
assert property (AddOneeotid_3);

property CarrySynceotid; @(posedge clk_in_1) (A) &&  (B) &&  (CIN) |->  (COUT) ;endproperty
assert property (CarrySynceotid);

property CarrySynceotid_2; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) |->  (COUT) ;endproperty
assert property (CarrySynceotid_2);

property CarrySynceotid_3; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (CIN) |->  (COUT) ;endproperty
assert property (CarrySynceotid_3);

property CarrySynceotid_4; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) |->  (COUT) ;endproperty
assert property (CarrySynceotid_4);

property AddOneeotid_4; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) |->  (SUM) ;endproperty
assert property (AddOneeotid_4);

property AddOneeotid_5; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) |->  (  !SUM ) ;endproperty
assert property (AddOneeotid_5);

property AddOneeotid_6; @(posedge clk_in_1) (  !A  ) ||  (  !B  ) ||  (  !CIN  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_6);

property AddOneeotid_7; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_7);

property AddOneeotid_8; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_8);

property AddOneeotid_9; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_9);

property AddOneeotid_10; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_10);

property AddOneeotid_11; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_11);

property AddOneeotid_12; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_12);

property AddOneeotid_13; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_13);

property AddOneeotid_14; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_14);

property AddOneeotid_15; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_15);

property AddOneeotid_16; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_16);

property AddOneeotid_17; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_17);

property AddOneeotid_18; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_18);

property AddOneeotid_19; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_19);

property AddOneeotid_20; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_20);

property AddOneeotid_21; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_21);

property AddOneeotid_22; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_22);

property AddOneeotid_23; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_23);

property AddOneeotid_24; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_24);

property AddOneeotid_25; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_25);

property AddOneeotid_26; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_26);

property AddOneeotid_27; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_27);

property AddOneeotid_28; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_28);

property AddOneeotid_29; @(posedge clk_in_1) (A) ||  (B) ||  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_29);

property AddOneeotid_30; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_30);

property AddOneeotid_31; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_31);

property AddOneeotid_32; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (CIN) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_32);

property AddOneeotid_33; @(posedge clk_in_1) (  !A  ) &&  (B) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_33);

property AddOneeotid_34; @(posedge clk_in_1) (A) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (COUT) ;endproperty
assert property (AddOneeotid_34);

property AddOneeotid_35; @(posedge clk_in_1) (  !A  ) &&  (  !B  ) &&  (  !CIN  ) &&  (  !SUM  ) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_35);

property AddOneeotid_36; @(posedge clk_in_1) (A) &&  (B) &&  (  !CIN  ) &&  (SUM) |->  (  !COUT ) ;endproperty
assert property (AddOneeotid_36);

endmodule