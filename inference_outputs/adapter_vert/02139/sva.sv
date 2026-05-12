property ClockSynceotid; @(posedge clk) (a) |-> (mux_out) == 4'b0001 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (b) |-> (mux_out) == 4'b0010 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (c) |-> (mux_out) == 4'b0100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) && (b) && (c) |-> (mux_out) == 4'b1000 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) != (b) && (b) != (c) && (a) != (c)  |-> (mux_out) == 4'b0011 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) != (b)  && (b) != (c) && (a) == (c)  |-> (mux_out) == 4'b0110 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) != (b)  && (b) == (c) && (a) != (c)  |-> (mux_out) == 4'b1100 ; endproperty 
 
 property ClockSynceotid; @(posedge clk) (a) != (b)  && (b) == (c) && (a) == (c)  |-> (mux_out) == 4'b1111 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) |-> (flip_flops_out) == 8'b00000000 && (counter) == 3'b000; endproperty 
 
 property ResetSynceotid; @(posedge clk) (reset) != 1'b1  && (counter) != 3'b111 |-> (flip_flops_out) == (d) && (counter) == 3'b000; endproperty 
 
 property SyncCtrleotid; @(posedge clk) (reset) != 1'b1  && (counter)  == 3'b111  |-> (flip_flops_out) == (d) && (counter) == 3'b000; endproperty 
 
 property SyncCtrleotid; @(posedge clk) (reset) != 1'b1  && (counter) != 3'b111  |-> (counter) == (counter) + 1; endproperty 
 
 property SyncFloweotid; @(posedge clk)  (  clk  &&  reset  &&  d  !=  q ) |->  (  q  ==  d  &&  counter  ==  3'b000 ) ; endproperty 
 