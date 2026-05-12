property ClockSynceotid; @(posedge clk) (dout) |-> (dout) == (din); endproperty 
 
 property SyncCheckeotid; @(posedge clk) (ctrl) && (sel) &&  (  (ctrl) && (sel)  != 7'b0000000 )  |->  (  (dout)  ==  (din)  ) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (ctrl) && (  !(sel)  )  &&  (  (ctrl)  != 7'b0000000 )  |->  (  (dout)  ==  (din)  ) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (  !(ctrl)  )  &&  (  (sel)  != 0 )  |->  (  (dout)  ==  (din)  ) ; endproperty 
 
 property SyncCheckeotid; @(posedge clk) (  !(ctrl)  )  &&  (  !(sel)  )  |->  (  (dout)  ==  (din)  ) ; endproperty 
 