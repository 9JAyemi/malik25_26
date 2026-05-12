property ClockSynceotid; @(posedge clk_in_1) (b) == ( !B1_N ) ;endproperty 
 
 property SyncIneotid; @(posedge clk_in_1) (and0_out) == (  A1  &&  A2  ) ;endproperty 
 
 property SyncCheckeotid; @(posedge clk_in_1) (nor0_out_Y) == (  !(b)  &&  !(and0_out)  ) ;endproperty 
 
 property SyncSafeeotid; @(posedge clk_in_1) (Y) == (  !(b)  &&  !(and0_out)  ) ;endproperty 
 