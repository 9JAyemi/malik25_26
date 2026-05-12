property ResetSynceotid; @(posedge clk) (rst) |-> (activate == 0) && (data == 0) && (strobe == 0) && (count == 0) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) (rst) |-> (strobe == 0) ;endproperty 
 
 property ReadySynceotid; @(posedge clk) (rst) &&  ( (ready > 0) && (activate == 0) && enable )  |->  (count == 0) && (  (ready[0]) && (  activate[0] == 1 )  ) ;endproperty 
 
 property ReadySynceotid; @(posedge clk) (rst) &&  ( (ready > 0) && (activate == 0) && enable )  &&  ( !(ready[0])  )  |->  (  activate[1] == 1 ) ;endproperty 
 
 property ActiveSynceotid; @(posedge clk) ! (rst)  &&  (  (ready > 0) && (activate == 0) && enable  ) |->  (  data  ==  count ) && (  count  ==  (  data  +  1 )  ) && (  strobe  ==  1 ) ;endproperty 
 
 property SafeReseteotid; @(posedge clk) ! (rst)  &&  (  (ready > 0) && (activate == 0) && enable  )  &&  (  (ready > 0) && (activate == 0) && enable  ) &&  (  activate > 0  )  |->  (  activate  !=  0 ) ;endproperty 
 
 property ResetSynceotid; @(posedge clk) ! (rst)  &&  (  !(ready > 0)  &&  (  activate > 0  )  ) |->  (  activate  ==  0 ) ;endproperty 
 