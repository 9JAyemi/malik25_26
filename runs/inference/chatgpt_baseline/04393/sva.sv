module omsp_sync_cell_sva (
    input logic        data_out,
    input logic        clk,
    input logic        data_in,
    input logic        rst,
    input logic [1:0]  data_sync
);

    // Output is driven from the second synchronizer stage.
    check_output_matches_stage1: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        data_out === data_sync[1]
    );

    // A sampled reset clears both stages and the output.
    check_reset_clears_state: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |-> ((data_sync === 2'b00) && (data_out === 1'b0))
    );

    // Reset keeps the synchronizer cleared through the next clock.
    check_reset_holds_clear_to_next_clock: assert property (
        @(posedge clk) disable iff ($initstate)
        rst |=> ((data_sync === 2'b00) && (data_out === 1'b0))
    );

    // The first stage captures the input on the next clock.
    check_stage0_captures_input: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        1'b1 |=> (data_sync[0] === $past(data_in))
    );

    // The second stage captures the prior first-stage value.
    check_stage1_captures_stage0: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        1'b1 |=> (data_sync[1] === $past(data_sync[0]))
    );

    // The output reflects the prior first-stage value on the next clock.
    check_output_follows_stage0: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        1'b1 |=> (data_out === $past(data_sync[0]))
    );

    // The output reflects the input after two clocks.
    check_output_follows_input_after_two_clocks: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        1'b1 |=> ##1 (data_out === $past(data_in,2))
    );

endmodule