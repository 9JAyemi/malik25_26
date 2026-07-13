module gray_shift_register_sva (
    input logic CLK,
    input logic RST,
    input logic counter_out,
    input logic data_in,
    input logic final_output,
    input logic gray_counter_out,
    input logic load,
    input logic select,
    input logic shift,
    input logic shift_reg,
    input logic shift_reg_out,
    input logic b0,
    input logic b00000000,
    input logic b1
);

property ResetSynceotid; @(posedge CLK) (RST) |-> gray_counter_out == 8'b00000000 && shift_reg == 8'b00000000 ;endproperty
assert property (ResetSynceotid);

property SyncLoadeotid; @(posedge CLK) (RST) != 1'b1 &&  (load) |-> shift_reg  == data_in ;endproperty
assert property (SyncLoadeotid);

property ShiftOneotid; @(posedge CLK) (RST) != 1'b1 &&  !(load) &&  (shift) |-> shift_reg  == {shift_reg[6:0], 1'b0} ;endproperty
assert property (ShiftOneotid);

property SyncCtrleotid; @(posedge CLK) (RST) != 1'b1  |-> counter_out == gray_counter_out ^ (gray_counter_out >> 1) && shift_reg_out == shift_reg ^ (shift_reg >> 1) ;endproperty
assert property (SyncCtrleotid);

property SyncCheckeotid; @(posedge CLK) (RST) != 1'b1  &&  (select) |-> final_output  == shift_reg_out ;endproperty
assert property (SyncCheckeotid);

property ResetSynceotid_2; @(posedge CLK) (RST) != 1'b1  &&  !(select)  |-> final_output  == counter_out ;endproperty
assert property (ResetSynceotid_2);

endmodule