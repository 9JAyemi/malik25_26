property MagnitudeCheckeotid; @(posedge clk_in_1) ( |A ) && (  |B  ) |-> ( |A ) > (  |B  ) && (  out  == 1 ) ;endproperty 
 
 property ValidDataeotid; @(posedge clk_in_1) ( |A ) && (  |B  ) |-> ( |A ) <= (  |B  ) && (  out  == 0 ) ;endproperty 
 