property ClockSynceotid; @(posedge clk_osc_15) (D) |-> (buf_mux_out) ;endproperty 
 
 property SyncIneotid; @(posedge clk_osc_15) (D) &&  (  (sel_0) &&  (sel_1)  ) |-> (mux_out) == (in_0) ;endproperty 
 
 property SyncIneotid; @(posedge clk_osc_15) (D) &&  (  (sel_0) && !(sel_1)  ) |-> (mux_out) == (in_1) ;endproperty 
 
 property SyncIneotid; @(posedge clk_osc_15) (D) &&  (  !(sel_0)  &&  (sel_1)  ) |-> (mux_out) == 1'b0 ;endproperty 
 