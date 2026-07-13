module cdc_3ff_sva #(
    parameter DATA_WIDTH = 1,
    parameter INIT_VALUE = 0
) (
    input logic target_clk,
    input logic reset,
    input logic [DATA_WIDTH-1:0] input_signal,
    input logic [DATA_WIDTH-1:0] output_signal,
    input logic [DATA_WIDTH-1:0] signal_meta,
    input logic [DATA_WIDTH-1:0] signal_d
);

    // A sampled reset leaves all three stages at INIT_VALUE on the next clock.
    check_reset_clears_all_stages_next_clock: assert property (
        @(posedge target_clk)
        reset |=> (signal_meta == INIT_VALUE) &&
                  (signal_d == INIT_VALUE) &&
                  (output_signal == INIT_VALUE)
    );

    // The first stage captures input_signal on the next target clock.
    check_signal_meta_captures_input: assert property (
        @(posedge target_clk) disable iff (reset)
        1'b1 |=> (signal_meta == $past(input_signal))
    );

    // The second stage captures signal_meta on the next target clock.
    check_signal_d_captures_signal_meta: assert property (
        @(posedge target_clk) disable iff (reset)
        1'b1 |=> (signal_d == $past(signal_meta))
    );

    // The output stage captures signal_d on the next target clock.
    check_output_captures_signal_d: assert property (
        @(posedge target_clk) disable iff (reset)
        1'b1 |=> (output_signal == $past(signal_d))
    );

    // input_signal reaches signal_d after two target clocks.
    check_signal_d_matches_input_after_two_clocks: assert property (
        @(posedge target_clk) disable iff (reset)
        1'b1 |=> ##1 (signal_d == $past(input_signal, 2))
    );

    // input_signal reaches output_signal after three target clocks.
    check_output_matches_input_after_three_clocks: assert property (
        @(posedge target_clk) disable iff (reset)
        1'b1 |=> ##2 (output_signal == $past(input_signal, 3))
    );

    // signal_d stays at INIT_VALUE for two clocks after a reset sample.
    check_signal_d_stays_init_two_clocks_after_reset: assert property (
        @(posedge target_clk)
        reset |=> (signal_d == INIT_VALUE) ##1 (signal_d == INIT_VALUE)
    );

    // output_signal stays at INIT_VALUE for three clocks after a reset sample.
    check_output_stays_init_three_clocks_after_reset: assert property (
        @(posedge target_clk)
        reset |=> (output_signal == INIT_VALUE) ##1
                  (output_signal == INIT_VALUE) ##1
                  (output_signal == INIT_VALUE)
    );

endmodule

bind cdc_3ff cdc_3ff_sva #(
    .DATA_WIDTH(DATA_WIDTH),
    .INIT_VALUE(INIT_VALUE)
) cdc_3ff_sva_i (
    .target_clk(target_clk),
    .reset(reset),
    .input_signal(input_signal),
    .output_signal(output_signal),
    .signal_meta(signal_meta),
    .signal_d(signal_d)
);