property AddSynceotid; @(posedge clk) (SEL[1]) |-> result == shift_out ; endproperty 
 
 property AddSynceotid; @(posedge clk) (SEL[1]) |->  (  (  A  -  B  )  ==  result  ) ; endproperty 
 
 property AddSynceotid; @(posedge clk) ( ! SEL[1] )  |->  (  (  A  +  B  )  ==  result  ) ; endproperty 
 