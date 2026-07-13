property ClockSynceotid; @(posedge clk_in_1) (a) && (b) |-> (mux_out) == (b) ; endproperty 
 
 property ValidInputeotid; @(posedge clk_in_1) (a) && ! (b)  &&  (sel_b1)  &&  (sel_b2)  ||  ! (a)  &&  (b)  &&  (sel_b1)  &&  (sel_b2)  ||  ! (a)  && ! (b)  &&  ! (sel_b1)  &&  ! (sel_b2)  == (mux_out); endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) != 7'b0000000 |-> pos == 3'b000 ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) == 7'b0000001  &&  (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  ! (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  (sel_b1)  &&  ! (sel_b2)  ||  (in) != 7'b0000001  && ! (sel_b1)  && ! (sel_b2)  == (pos); endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) != 7'b0000000  &&  (pos) == 3'b000  |-> (out_sum) == (mux_out) ; endproperty 
 
 property ValidIneotid; @(posedge clk_in_1) (in) == 7'b0000001  &&  (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  ! (sel_b1)  &&  (sel_b2)  ||  (in) != 7'b0000001  &&  (sel_b1)  &&  ! (sel_b2)  ||  (in) != 7'b0000001  && ! (sel_b1)  && ! (sel_b2)  == (out_sum); endproperty 
 