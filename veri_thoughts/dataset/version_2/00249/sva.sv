module DemoInterconnect_jtag_axi_0_0_rd_status_flags_as__parameterized0_22_sva (
    input logic out,
    input logic [1:0] dest_out_bin_ff_reg,
    input logic aclk,
    input logic ram_empty_fb_i,
    input logic ram_empty_i
);

    // out mirrors the first-stage flag.
    check_out_matches_feedback_flag: assert property (
        @(posedge aclk) out == ram_empty_fb_i
    );

    // The first stage captures dest_out_bin_ff_reg[1] each cycle.
    check_feedback_flag_captures_dest_msb: assert property (
        @(posedge aclk) 1'b1 |=> (ram_empty_fb_i == $past(dest_out_bin_ff_reg[1]))
    );

    // The second stage captures the first-stage flag each cycle.
    check_empty_flag_captures_feedback_flag: assert property (
        @(posedge aclk) 1'b1 |=> (ram_empty_i == $past(ram_empty_fb_i))
    );

    // The output is a one-cycle delayed copy of dest_out_bin_ff_reg[1].
    check_out_is_one_cycle_delayed_dest_msb: assert property (
        @(posedge aclk) 1'b1 |=> (out == $past(dest_out_bin_ff_reg[1]))
    );

    // The second stage matches the previous cycle output.
    check_empty_flag_matches_previous_out: assert property (
        @(posedge aclk) 1'b1 |=> (ram_empty_i == $past(out))
    );

    // The second stage is a two-cycle delayed copy of dest_out_bin_ff_reg[1].
    check_empty_flag_is_two_cycle_delayed_dest_msb: assert property (
        @(posedge aclk) 1'b1 |-> ##2 (ram_empty_i == $past(dest_out_bin_ff_reg[1], 2))
    );

endmodule