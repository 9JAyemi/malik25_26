module comparator_4bit_sva (
    input logic A,
    input logic A_reg,
    input logic B,
    input logic B_reg,
    input logic EQ,
    input logic GT,
    input logic LT,
    input logic enable,
    input logic load_A,
    input logic load_B,
    input logic reset,
    input logic b0,
    input logic b1,
    input logic clk_reset_17
);

property ResetSynceotid; @(negedge clk_reset_17) (reset) |-> (A_reg == 4'b0) && (B_reg == 4'b0) && (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0) ;endproperty
assert property (ResetSynceotid);

property ResetSynceotid_2; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) |-> (A_reg == A) ;endproperty
assert property (ResetSynceotid_2);

property ResetSynceotid_3; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_B) |-> (B_reg == B) ;endproperty
assert property (ResetSynceotid_3);

property ResetSynceotid_4; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg == B_reg) |-> (EQ == 1'b1) && (GT == 1'b0) && (LT == 1'b0) ;endproperty
assert property (ResetSynceotid_4);

property ResetSynceotid_5; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg != B_reg) &&  (A_reg > B_reg) |-> (EQ == 1'b0) && (GT == 1'b1) && (LT == 1'b0) ;endproperty
assert property (ResetSynceotid_5);

property ResetSynceotid_6; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg != B_reg) &&  (A_reg <= B_reg) |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b1) ;endproperty
assert property (ResetSynceotid_6);

property ResetSynceotid_7; @(negedge clk_reset_17) ! (reset)  &&  ! (enable)  |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0) ;endproperty
assert property (ResetSynceotid_7);

endmodule