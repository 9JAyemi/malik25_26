module karnaugh_map_sva (
    input logic A,
    input logic B,
    input logic C,
    input logic D,
    input logic E,
    input logic F,
    input logic clk_reset_13
);

property ResetSynceotid; @(negedge clk_reset_13) (A) && (B) && (C) && (D) &&  (E) |-> (F) == 1 ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_13) (A) && (B) && (C) &&  (D) && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_13) (A) && (B) &&  (C) && ! (D)  &&  (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_13) (A) && (B) &&  (C) && ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_13)  (A)  && ! (B)  && (C) && (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_13)  (A)  && ! (B)  && (C) && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_13)  (A)  && ! (B)  && (C) &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(negedge clk_reset_13)  (A)  && ! (B)  && (C) &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(negedge clk_reset_13) ! (A)  && (B)  && (C) && (D)  &&  (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(negedge clk_reset_13) ! (A)  && (B)  && (C) && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(negedge clk_reset_13) ! (A)  && (B)  && (C) &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(negedge clk_reset_13) ! (A)  && (B)  && (C) &&  ! (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(negedge clk_reset_13) ! (A)  && ! (B)  && (C) && (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(negedge clk_reset_13) ! (A)  && ! (B)  && (C) && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(negedge clk_reset_13) ! (A)  && ! (B)  && (C) &&  ! (D)  &&  (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(negedge clk_reset_13) ! (A)  && ! (B)  && (C) &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_16);

property ResetSynceotid_17; @(negedge clk_reset_13)  (A)  && (B)  && ! (C)  && (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_17);

property ResetSynceotid_18; @(negedge clk_reset_13)  (A)  && (B)  && ! (C)  && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_18);

property ResetSynceotid_19; @(negedge clk_reset_13)  (A)  && (B)  && ! (C)  &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_19);

property ResetSynceotid_20; @(negedge clk_reset_13)  (A)  && (B)  && ! (C)  &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_20);

property ResetSynceotid_21; @(negedge clk_reset_13) ! (A)  &&  (B)  && ! (C)  && (D)  &&  (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_21);

property ResetSynceotid_22; @(negedge clk_reset_13) ! (A)  &&  (B)  && ! (C)  && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_22);

property ResetSynceotid_23; @(negedge clk_reset_13) ! (A)  &&  (B)  && ! (C)  &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_23);

property ResetSynceotid_24; @(negedge clk_reset_13) ! (A)  &&  (B)  && ! (C)  &&  ! (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_24);

property ResetSynceotid_25; @(negedge clk_reset_13)  (A)  && ! (B)  && ! (C)  && (D)  &&  (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_25);

property ResetSynceotid_26; @(negedge clk_reset_13)  (A)  && ! (B)  && ! (C)  && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_26);

property ResetSynceotid_27; @(negedge clk_reset_13)  (A)  && ! (B)  && ! (C)  &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_27);

property ResetSynceotid_28; @(negedge clk_reset_13)  (A)  && ! (B)  && ! (C)  &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_28);

property ResetSynceotid_29; @(negedge clk_reset_13) ! (A)  && (B)  &&  (C)  && (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_29);

property ResetSynceotid_30; @(negedge clk_reset_13) ! (A)  && (B)  &&  (C)  && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_30);

property ResetSynceotid_31; @(negedge clk_reset_13) ! (A)  && (B)  &&  (C)  &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_31);

property ResetSynceotid_32; @(negedge clk_reset_13) ! (A)  && (B)  &&  (C)  &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_32);

property ResetSynceotid_33; @(negedge clk_reset_13)  (A)  && ! (B)  &&  (C)  && (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_33);

property ResetSynceotid_34; @(negedge clk_reset_13)  (A)  && ! (B)  &&  (C)  && (D)  && ! (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_34);

property ResetSynceotid_35; @(negedge clk_reset_13)  (A)  && ! (B)  &&  (C)  &&  ! (D)  &&  (E)  |-> (F) == 1 ;endproperty
assert property (ResetSynceotid_35);

property ResetSynceotid_36; @(negedge clk_reset_13)  (A)  && ! (B)  &&  (C)  &&  ! (D)  && ! (E)  |-> (F) == 0 ;endproperty
assert property (ResetSynceotid_36);

endmodule