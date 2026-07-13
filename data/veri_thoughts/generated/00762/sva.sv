module pipeline_register_sva (
    input logic clock,
    input logic reset,
    input logic IF_Flush,
    input logic IF_Stall,
    input logic ID_Stall,
    input logic [31:0] IF_Instruction,
    input logic [31:0] IF_PCAdd4,
    input logic [31:0] IF_PC,
    input logic IF_IsBDS,
    input logic [31:0] ID_Instruction,
    input logic [31:0] ID_PCAdd4,
    input logic [31:0] ID_RestartPC,
    input logic ID_IsBDS,
    input logic ID_IsFlushed,
    input logic [31:0] vote_ID_Instruction,
    input logic [31:0] vote_ID_PCAdd4,
    input logic [31:0] vote_ID_RestartPC,
    input logic vote_ID_IsBDS,
    input logic vote_ID_IsFlushed
);
    // On reset, all outputs clear to zero on the next cycle.
    reset_clears_outputs: assert property (
        @(posedge clock) reset |=> (vote_ID_Instruction == 32'b0)
                            && (vote_ID_PCAdd4 == 32'b0)
                            && (vote_ID_RestartPC == 32'b0)
                            && (vote_ID_IsBDS == 1'b0)
                            && (vote_ID_IsFlushed == 1'b0)
    );

    // When ID_Stall is asserted, data fields capture from ID_* on the next cycle.
    id_stall_captures_id_data: assert property (
        @(posedge clock) disable iff (reset)
            ID_Stall |=> (vote_ID_Instruction == $past(ID_Instruction))
                      && (vote_ID_PCAdd4    == $past(ID_PCAdd4))
                      && (vote_ID_RestartPC == $past(ID_RestartPC))
    );

    // When !ID_Stall and IF_Stall or IF_Flush, instruction and PCAdd4 zero on next cycle.
    zero_if_fields_on_if_stall_or_flush: assert property (
        @(posedge clock) disable iff (reset)
            (!ID_Stall && (IF_Stall || IF_Flush)) |=> (vote_ID_Instruction == 32'b0)
                                                  && (vote_ID_PCAdd4 == 32'b0)
    );

    // When !ID_Stall and no IF_Stall/Flush, instruction and PCAdd4 pass through from IF_*.
    pass_if_fields_when_no_if_controls: assert property (
        @(posedge clock) disable iff (reset)
            (!ID_Stall && !(IF_Stall || IF_Flush)) |=> (vote_ID_Instruction == $past(IF_Instruction))
                                                   && (vote_ID_PCAdd4    == $past(IF_PCAdd4))
    );

    // When !ID_Stall and (ID_IsFlushed or IF_IsBDS), RestartPC comes from ID_RestartPC.
    restartpc_selects_id_on_flush_or_bds: assert property (
        @(posedge clock) disable iff (reset)
            (!ID_Stall && (ID_IsFlushed || IF_IsBDS)) |=> (vote_ID_RestartPC == $past(ID_RestartPC))
    );

    // When !ID_Stall and not (ID_IsFlushed or IF_IsBDS), RestartPC comes from IF_PC.
    restartpc_selects_if_on_normal_flow: assert property (
        @(posedge clock) disable iff (reset)
            (!ID_Stall && !(ID_IsFlushed || IF_IsBDS)) |=> (vote_ID_RestartPC == $past(IF_PC))
    );

    // vote_ID_IsBDS always reflects prior-cycle ID_IsBDS (outside reset).
    flags_follow_id_isbds: assert property (
        @(posedge clock) disable iff (reset)
            1'b1 |=> (vote_ID_IsBDS == $past(ID_IsBDS))
    );

    // vote_ID_IsFlushed always reflects prior-cycle ID_IsFlushed (outside reset).
    flags_follow_id_isflushed: assert property (
        @(posedge clock) disable iff (reset)
            1'b1 |=> (vote_ID_IsFlushed == $past(ID_IsFlushed))
    );
endmodule