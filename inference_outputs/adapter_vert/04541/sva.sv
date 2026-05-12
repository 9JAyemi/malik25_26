property ClockSynceotid; @(posedge clk_in_1) (invert) |-> (Y) == ( ~ (  ~ ( A )  + 1'b1 ) ); endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (invert) &&  (  ~ (  ~ ( A )  + 1'b1 )  !=  (  ~ ( A )  + 1'b1 ) ) |-> (Y) != (  ~ ( A )  + 1'b1 ); endproperty 
 
 property ClockSynceotid; @(posedge clk_in_1) (  ~ (  ~ ( A )  + 1'b1 )  &&  (  ~ (  ~ ( A )  + 1'b1 )  !=  (  ~ ( A )  + 1'b1 )  ) ) |-> (Y) == (  ~ ( A )  + 1'b1 ); endproperty 
 