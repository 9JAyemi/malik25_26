property SyncEqeotid; @(posedge clk_in_14) (A) == (B) |-> (equal) ; endproperty 
 
 property PosSynceotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  >  $signed (B)  ) |-> (signed_larger) ; endproperty 
 
 property SignedSmalleotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  <  $signed (B)  ) |-> (signed_smaller) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) == (B) |->  (  out  ==  0 ) ; endproperty 
 
 property ShiftOnRiseeotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  >  $signed (B)  ) |->  (  out  ==  shifted_num ) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_14) (A) != (B) &&  (  $signed (A)  <  $signed (B)  ) |->  (  out  ==  smaller_num ) ; endproperty 
 