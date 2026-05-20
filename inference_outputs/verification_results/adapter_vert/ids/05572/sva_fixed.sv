module hexledx_sva (
    input logic blank,
    input logic minus,
    input logic s7,
    input logic value,
    input logic b0000110,
    input logic b0000111,
    input logic b0111001,
    input logic b0111111,
    input logic b1001111,
    input logic b1011011,
    input logic b1100110,
    input logic b1101101,
    input logic b1101111,
    input logic b1110111,
    input logic b1111100,
    input logic b1111101,
    input logic clk_reset_19,
    input logic h0,
    input logic h1,
    input logic h2,
    input logic h3,
    input logic h4,
    input logic h5,
    input logic h6,
    input logic h7,
    input logic h8,
    input logic h9,
    input logic hA,
    input logic hB,
    input logic hC
);

property ResetSynceotid; @(negedge clk_reset_19) (blank) |-> s7 == 7'b0111111 ; endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_19) (blank) &&  (  ! (  minus  )  ) |-> s7 == 7'b0000110 ; endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_19) (  minus  ) |-> s7 == 7'b1011011 ; endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_19) (  minus  ) &&  (  ! (  blank  )  ) |-> s7 == 7'b1001111 ; endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  == 4'h0 )  ) |-> s7 == 7'b1100110 ; endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  == 4'h1 )  ) |-> s7 == 7'b1101101 ; endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  == 4'h2 )  ) |-> s7 == 7'b1111101 ; endproperty
assert property (ResetSynceotid_7);

property ResetSynceotid_8; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  == 4'h3 )  ) |-> s7 == 7'b0000111 ; endproperty
assert property (ResetSynceotid_8);

property ResetSynceotid_9; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  == 4'h4 )  ) |-> s7 == 7'b1100110 ; endproperty
assert property (ResetSynceotid_9);

property ResetSynceotid_10; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  == 4'h5 )  ) |-> s7 == 7'b1101101 ; endproperty
assert property (ResetSynceotid_10);

property ResetSynceotid_11; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  == 4'h6 )  ) |-> s7 == 7'b1111101 ; endproperty
assert property (ResetSynceotid_11);

property ResetSynceotid_12; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  == 4'h7 )  ) |-> s7 == 7'b0000111 ; endproperty
assert property (ResetSynceotid_12);

property ResetSynceotid_13; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  == 4'h8 )  ) |-> s7 == 7'b1100110 ; endproperty
assert property (ResetSynceotid_13);

property ResetSynceotid_14; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  == 4'h9 )  ) |-> s7 == 7'b1101111 ; endproperty
assert property (ResetSynceotid_14);

property ResetSynceotid_15; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  == 4'hA )  ) |-> s7 == 7'b1110111 ; endproperty
assert property (ResetSynceotid_15);

property ResetSynceotid_16; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  != 4'hA )  &&  (  value  == 4'hB )  ) |-> s7 == 7'b1111100 ; endproperty
assert property (ResetSynceotid_16);

property ResetSynceotid_17; @(negedge clk_reset_19) (  !blank  ) &&  (  ! (  minus  )  &&  (  value  != 4'h0 ) &&  (  value  != 4'h1 )  &&  (  value  != 4'h2 )  &&  (  value  != 4'h3 )  &&  (  value  != 4'h4 )  &&  (  value  != 4'h5 )  &&  (  value  != 4'h6 )  &&  (  value  != 4'h7 )  &&  (  value  != 4'h8 )  &&  (  value  != 4'h9 )  &&  (  value  != 4'hA )  &&  (  value  != 4'hB )  &&  (  value  == 4'hC )  ) |-> s7 == 7'b0111001 ; endproperty
assert property (ResetSynceotid_17);

endmodule