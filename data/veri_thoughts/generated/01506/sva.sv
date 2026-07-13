module IF_ID_sva (
    input logic clk,
    input logic rst,
    input logic stall,
    input logic BJ,
    input logic [31:0] if_pcplus4,
    input logic [31:0] if_instr,
    input logic [31:0] if_pc,
    input logic [31:0] id_pcplus4,
    input logic [31:0] id_instr,
    input logic [31:0] id_pc
);
    // During reset, id_pcplus4 drives 4.
    reset_id_pcplus4_value: assert property (
        @(posedge clk) rst |-> (id_pcplus4 == 32'd4)
    );
    // During reset, id_instr drives 32'b100000.
    reset_id_instr_value: assert property (
        @(posedge clk) rst |-> (id_instr == 32'b100000)
    );
    // During reset, id_pc drives 0.
    reset_id_pc_value: assert property (
        @(posedge clk) rst |-> (id_pc == 32'd0)
    );

    // id_pcplus4 captures if_pcplus4 each cycle (1-cycle latency).
    capture_id_pcplus4_every_cycle: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (id_pcplus4 == $past(if_pcplus4))
    );
    // id_pc captures if_pc each cycle (1-cycle latency).
    capture_id_pc_every_cycle: assert property (
        @(posedge clk) disable iff (rst) $past(!rst) |-> (id_pc == $past(if_pc))
    );

    // If stall or BJ in the previous cycle, id_instr flushes to 32'b100000.
    id_instr_flush_on_stall_or_BJ: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && (stall | BJ)) |-> (id_instr == 32'b100000)
    );
    // If neither stall nor BJ in the previous cycle, id_instr captures if_instr.
    id_instr_capture_when_no_stall_or_BJ: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && !(stall | BJ)) |-> (id_instr == $past(if_instr))
    );

    // A change in id_pcplus4 implies if_pcplus4 changed one cycle earlier.
    id_pcplus4_change_implies_input_change: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst,2) && (id_pcplus4 != $past(id_pcplus4))) |-> ($past(if_pcplus4) != $past(if_pcplus4,2))
    );
    // A change in id_pc implies if_pc changed one cycle earlier.
    id_pc_change_implies_input_change: assert property (
        @(posedge clk) disable iff (rst) ($past(!rst,2) && (id_pc != $past(id_pc))) |-> ($past(if_pc) != $past(if_pc,2))
    );

    // On stall or BJ, id_pcplus4 and id_pc still update from IF stage.
    id_pc_updates_on_stall_or_BJ: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && (stall | BJ)) |-> (id_pcplus4 == $past(if_pcplus4)) && (id_pc == $past(if_pc))
    );
    // With no stall or BJ, id_pcplus4 and id_pc update from IF stage.
    id_pc_updates_when_no_stall_or_BJ: assert property (
        @(posedge clk) disable iff (rst) $past(!rst && !(stall | BJ)) |-> (id_pcplus4 == $past(if_pcplus4)) && (id_pc == $past(if_pc))
    );
endmodule