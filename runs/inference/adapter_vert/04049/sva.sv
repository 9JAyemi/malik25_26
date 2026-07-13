property ResetSynceotid; @(posedge clk) (resetn==0 || squashn==0) |-> q == 0 ; endproperty 
 
 property EnableSynceotid; @(posedge clk) (resetn!=0 && squashn!=0) && (en==1) |-> q == d ; endproperty 
 