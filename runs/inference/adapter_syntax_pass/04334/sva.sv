module RCB_FRL_TrainingPattern_sva (
    input logic CLK,
    input logic RST,
    input logic [7:0] DATA_OUT
);

    // Reset clears the output on the next clock.
    check_reset_clears_data_out: assert property (
        @(posedge CLK) RST |=> (DATA_OUT == 8'h00)
    );

    // The first cycle after reset deassertion still sees zero.
    check_post_reset_zero: assert property (
        @(posedge CLK) disable iff (RST) $fell(RST) |-> (DATA_OUT == 8'h00)
    );

    // The first non-reset cycle after 0xf4 returns 0xc2.
    check_f4_to_c2: assert property (
        @(posedge CLK) disable iff (RST) ($past(DATA_OUT) == 8'hf4) |-> (DATA_OUT == 8'hc2)
    );

    // Any non-0xf4 value returns 0xf4.
    check_non_f4_to_f4: assert property (
        @(posedge CLK) disable iff (RST) ($past(DATA_OUT) != 8'hf4) |-> (DATA_OUT == 8'hf4)
    );

    // The output is always either 0xf4 or 0xc2.
    check_output_legal_values: assert property (
        @(posedge CLK) disable iff (RST) (DATA_OUT inside {8'hf4, 8'hc2})
    );

endmodule