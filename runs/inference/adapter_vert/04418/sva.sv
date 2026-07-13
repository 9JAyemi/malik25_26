property ClockSynceotid; @(posedge clk) (select) |-> xor_input == in_2 ; endproperty 
 
 property SyncAddereotid; @(posedge clk) (select) |-> xor_output == (in_1 + in_2) ^ in_2 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (select) &&  (  !reset  ) |-> adder_output == in_1 + in_2 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (  !select  ) |-> xor_input == in_1 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (  !select  ) |-> xor_output == (in_1 + in_2) ^ in_1 ; endproperty 
 
 property ResetSynceotid; @(posedge clk) (  !select  ) &&  (  !reset  ) |-> adder_output == in_1 + in_2 ; endproperty 
 