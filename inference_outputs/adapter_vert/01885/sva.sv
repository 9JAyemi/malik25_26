property ClockSynceotid; @(posedge clk) (en) |-> data == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00001 ) |-> data == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00010 ) |-> data == 4'b1110 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00011 ) |-> data == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00100 ) |-> data == 4'b0100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00101 ) |-> data == 4'b1010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00110 ) |-> data == 4'b1100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b00111 ) |-> data == 4'b0000 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01000 ) |-> data == 4'b1010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01001 ) |-> data == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01010 ) |-> data == 4'b1110 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01011 ) |-> data == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01100 ) |-> data == 4'b0100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01101 ) |-> data == 4'b1010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01110 ) |-> data == 4'b1100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (en) && ( addr == 5'b01111 ) |-> data == 4'b0000 ; endproperty 
 
 property SafeAccesseotid; @(posedge clk) ! (en)  |-> data == 4'bXXXX ; endproperty 
 