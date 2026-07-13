property ResetSynceotid; @(negedge clk_reset_19) (A) && (B) && (C) |-> (F) == (m0) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) && (B) && (!C) |-> (F) == (m1) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) && (!B) && (C) |-> (F) == (m2) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) && (!B) && (!C) |-> (F) == (m3) ; endproperty 
 
 property ResetSynceotid; @(negedge clk_reset_19) (A) && (B) && (C) || (A) && (B) && (!C) || (A) && (!B) && (C) || (A) && (!B) && (!C) |-> (F) == (m0) || (F) == (m1) || (F) == (m2) || (F) == (m3) ; endproperty 
 