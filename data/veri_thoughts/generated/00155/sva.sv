module trigger_control_sva (
    input logic        clk,
    input logic        sync,
    input logic        reset,

    input logic        sel_async,
    input logic        sel_sync,
    input logic        sel_single,
    input logic        sel_gen,
    input logic        sel_pg,
    input logic        sel_dir_async,
    input logic        sel_dir_sync,
    input logic        sel_dir_single,
    input logic        sel_dir_gen,
    input logic        sel_dir_pg,
    input logic        sel_chain,
    input logic        sel_sync_out,
    input logic [4:0]  src_async,
    input logic [3:0]  src_async_pos,

    input logic [4:0]  src_sync,
    input logic        src_sync_direct,

    input logic [4:0]  src_single,
    input logic [4:0]  src_gen,
    input logic [4:0]  src_pg,
    input logic [4:0]  dst_tbm,
    input logic [3:0]  dst_tbm_pos,

    input logic [4:0]  dst_sync,
    input logic        dst_sync_direct,

    input logic [4:0]  dst_dir
);

    // dst_tbm is the OR of all enabled trigger sources.
    check_dst_tbm_selection: assert property (
        @(posedge clk) disable iff (reset)
        dst_tbm == (({5{sel_async}}  & src_async)  |
                    ({5{sel_sync}}   & src_sync)   |
                    ({5{sel_single}} & src_single) |
                    ({5{sel_gen}}    & src_gen)    |
                    ({5{sel_pg}}     & src_pg))
    );

    // dst_sync_direct only passes src_sync_direct when chaining is enabled.
    check_dst_sync_direct_chain: assert property (
        @(posedge clk) disable iff (reset)
        dst_sync_direct == (sel_chain & src_sync_direct)
    );

    // dst_sync is gated by sel_sync_out and blocked by sel_chain.
    check_dst_sync_selection: assert property (
        @(posedge clk) disable iff (reset)
        dst_sync == ({5{sel_sync_out & !sel_chain}} & dst_tbm)
    );

    // dst_tbm_pos is src_async_pos gated by sel_async and src_async[1].
    check_dst_tbm_pos_gate: assert property (
        @(posedge clk) disable iff (reset)
        dst_tbm_pos == (src_async_pos & {4{sel_async & src_async[1]}})
    );

    // dst_dir is the OR of all enabled direct sources.
    check_dst_dir_selection: assert property (
        @(posedge clk) disable iff (reset)
        dst_dir == (({5{sel_dir_async}}  & src_async)  |
                    ({5{sel_dir_sync}}   & src_sync)   |
                    ({5{sel_dir_single}} & src_single) |
                    ({5{sel_dir_gen}}    & src_gen)    |
                    ({5{sel_dir_pg}}     & src_pg))
    );

    // Chaining forces dst_sync low.
    check_chain_blocks_dst_sync: assert property (
        @(posedge clk) disable iff (reset)
        sel_chain |-> (dst_sync == 5'b0)
    );

    // With sync output enabled and no chain, dst_sync matches dst_tbm.
    check_enabled_sync_out_copies_tbm: assert property (
        @(posedge clk) disable iff (reset)
        (sel_sync_out && !sel_chain) |-> (dst_sync == dst_tbm)
    );

    // With sync output disabled, dst_sync is zero.
    check_disabled_sync_out_clears_dst_sync: assert property (
        @(posedge clk) disable iff (reset)
        !sel_sync_out |-> (dst_sync == 5'b0)
    );

    // If no main source is selected, dst_tbm is zero.
    check_no_main_selects_clear_dst_tbm: assert property (
        @(posedge clk) disable iff (reset)
        !(sel_async || sel_sync || sel_single || sel_gen || sel_pg) |-> (dst_tbm == 5'b0)
    );

    // If no direct source is selected, dst_dir is zero.
    check_no_dir_selects_clear_dst_dir: assert property (
        @(posedge clk) disable iff (reset)
        !(sel_dir_async || sel_dir_sync || sel_dir_single || sel_dir_gen || sel_dir_pg) |-> (dst_dir == 5'b0)
    );

endmodule