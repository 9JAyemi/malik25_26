property ClockSynceotid; @(posedge clk) (a) && (a > b) && (a > c) && (a > d) |-> priority_out == 2'b00 ; endproperty 
 
 property HighPrioSynceotid; @(posedge clk) (b) && (b > a) && (b > c) && (b > d) |-> priority_out == 2'b01 ; endproperty 
 
 property HighPrioSynceotid; @(posedge clk) (c) && (c > a) && (c > b) && (c > d) |-> priority_out == 2'b10 ; endproperty 
 
 property HighPrioSynceotid; @(posedge clk) (d) && (d > a) && (d > b) && (d > c) |-> priority_out == 2'b11 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) && (a > b) && (a > c) && (a > d) |-> mux_out == 8'h0 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (b) && (b > a) && (b > c) && (b > d) |-> mux_out == 8'h1 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (c) && (c > a) && (c > b) && (c > d) |-> mux_out == 8'h2 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (d) && (d > a) && (d > b) && (d > c) |-> mux_out == 8'h3 ; endproperty 
 
 property ValidDataeotid; @(posedge clk) (in) |-> (out_and) && (out_or) && (out_xor) ; endproperty 
 