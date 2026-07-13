property ClockSynceotid; @(posedge clk) (sel_b1) |-> selected_input_b1 == b ;endproperty 
 
 property SyncEqeotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  (sel_out) ) |-> selected_input_b2 == b ;endproperty 
 
 property XorSynceotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_xor == selected_input_b2 ^ a ;endproperty 
 
 property ValidXorSynceotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_xor_inv == ~out_xor ;endproperty 
 
 property ValidXorSynceotid; @(posedge clk) (sel_b1) &&  (  !(sel_b2)  &&  !(sel_out)  ) |-> out_logical_inv == !out_xor ;endproperty 
 
 property SyncEqeotid; @(posedge clk) (  !(sel_b1)  &&  (  !(sel_b2)  &&  (sel_out) ) ) |-> out_always == out_logical_inv ;endproperty 
 
 property SyncEqeotid; @(posedge clk) (  !(sel_b1)  &&  (  !(sel_b2)  &&  !(sel_out) ) ) |-> out_always == out_xor_inv ;endproperty 
 