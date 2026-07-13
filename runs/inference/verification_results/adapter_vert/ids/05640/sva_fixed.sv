module if_stage_sva (
    input logic IF_ID_instruction,
    input logic IF_ID_next_i_addr,
    input logic clk,
    input logic i_instr_in,
    input logic if_id_write_en,
    input logic mem_op,
    input logic next_i_addr,
    input logic pc_reg,
    input logic pc_write,
    input logic pstop_i,
    input logic rst,
    input logic pc_next
);

property ClockSynceotid; @(posedge clk) (rst) |-> pc_reg == 0 ;endproperty
assert property (ClockSynceotid);

property SyncCtrleotid; @(posedge clk) (pc_write && !(pstop_i || mem_op)) |-> pc_reg == pc_next ;endproperty
assert property (SyncCtrleotid);

property SyncValideotid; @(posedge clk) (if_id_write_en) |-> IF_ID_next_i_addr == next_i_addr && IF_ID_instruction == (  !(pstop_i || mem_op) ? i_instr_in : 0 );endproperty
assert property (SyncValideotid);

endmodule