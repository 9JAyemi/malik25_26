property ClockSynceotid; @(posedge clk) (rst) |-> pc_reg == 0 ;endproperty 
 
 property SyncCtrleotid; @(posedge clk) (pc_write && !(pstop_i || mem_op)) |-> pc_reg == pc_next ;endproperty 
 
 property SyncValideotid; @(posedge clk) (if_id_write_en) |-> IF_ID_next_i_addr == next_i_addr && IF_ID_instruction == (  !(pstop_i || mem_op) ? i_instr_in : 0 );endproperty 
 