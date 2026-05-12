property ResetSynceotid; @(posedge clk) (reset) |-> (count == 4'b0000) && (overflow == 1'b0) ;endproperty 
 
 property SafeCtrleotid; @(posedge clk) (reset) |-> (count != 4'b1111) ;endproperty 
 
 property SafeCtrleotid; @(posedge clk) (enable) &&  (  ! (reset)  &&  ! (count == 4'b1111)  ) |-> count == (count + 1) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (enable) &&  (  ! (reset)  &&  (count == 4'b1111)  ) |-> (count == 4'b0000) && (overflow == 1'b1) ;endproperty 
 