property ORANDeotid; @(posedge clk_osc_14) ( A ) |->  ( Y  != (  A  |  B  ) &  C  );endproperty 
 
 property ORANDeotid; @(posedge clk_osc_14) ( B ) |->  ( Y  != (  A  |  B  ) &  C  );endproperty 
 
 property ANDeotid; @(posedge clk_osc_14) ( C ) |->  ( Y  ==  (  A  |  B  ) &  C  );endproperty 
 