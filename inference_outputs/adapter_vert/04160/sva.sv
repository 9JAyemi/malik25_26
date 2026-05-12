property ResetSynceotid; @(posedge CLK) (RST) |-> gray_counter_out == 8'b00000000 && shift_reg == 8'b00000000 ;endproperty 
 
 property SyncLoadeotid; @(posedge CLK) (RST) != 1'b1 &&  (load) |-> shift_reg  == data_in ;endproperty 
 
 property ShiftOneotid; @(posedge CLK) (RST) != 1'b1 &&  !(load) &&  (shift) |-> shift_reg  == {shift_reg[6:0], 1'b0} ;endproperty 
 
 property SyncCtrleotid; @(posedge CLK) (RST) != 1'b1  |-> counter_out == gray_counter_out ^ (gray_counter_out >> 1) && shift_reg_out == shift_reg ^ (shift_reg >> 1) ;endproperty 
 
 property SyncCheckeotid; @(posedge CLK) (RST) != 1'b1  &&  (select) |-> final_output  == shift_reg_out ;endproperty 
 
 property ResetSynceotid; @(posedge CLK) (RST) != 1'b1  &&  !(select)  |-> final_output  == counter_out ;endproperty 
 