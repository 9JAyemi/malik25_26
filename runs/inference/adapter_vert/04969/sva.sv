property ResetSynceotid; @(negedge clk_reset_17) (reset) |-> (A_reg == 4'b0) && (B_reg == 4'b0) && (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) |-> (A_reg == A) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_B) |-> (B_reg == B) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg == B_reg) |-> (EQ == 1'b1) && (GT == 1'b0) && (LT == 1'b0) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg != B_reg) &&  (A_reg > B_reg) |-> (EQ == 1'b0) && (GT == 1'b1) && (LT == 1'b0) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) (reset) &&  (enable) &&  (load_A) &&  (load_B) &&  (A_reg != B_reg) &&  (A_reg <= B_reg) |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b1) ;endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_17) ! (reset)  &&  ! (enable)  |-> (EQ == 1'b0) && (GT == 1'b0) && (LT == 1'b0) ;endproperty 
 