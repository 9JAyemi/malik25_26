property ClockSynceotid; @(posedge clk_in_14) (in) |-> (out) == (in * 2) ; endproperty 
 
 property Squareeotid; @(posedge clk_in_14) (in) && ( in <= 7 ) |-> (out) == (in * in) ; endproperty 
 
 property DivBy2eotid; @(posedge clk_in_14) (in) &&  ( !(in < 4) && !(in <= 7)  )  |-> (out) == (in / 2) ; endproperty 
 