module RegisterAdd_6_sva (
    input logic add_overflow_flag,
    input logic [0:0] E,
    input logic [0:0] O,
    input logic CLK,
    input logic [0:0] AR
);

    // Overflow can only be high when both current input bits are high.
    check_overflow_requires_high_inputs: assert property (
        @(posedge CLK) disable iff (!AR[0])
        add_overflow_flag |-> ((E[0] == 1'b1) && (O[0] == 1'b1))
    );

    // If either current input bit is low, the overflow output must be low.
    check_low_input_blocks_overflow: assert property (
        @(posedge CLK) disable iff (!AR[0])
        ((E[0] == 1'b0) || (O[0] == 1'b0)) |-> (add_overflow_flag == 1'b0)
    );

    // While reset is asserted, the output must stay low.
    check_reset_forces_output_low: assert property (
        @(posedge CLK)
        (AR[0] == 1'b0) |-> (add_overflow_flag == 1'b0)
    );

    // A sampled reset cycle clears the registered contribution by the next clock.
    check_reset_clears_output_next_cycle: assert property (
        @(posedge CLK)
        (AR[0] == 1'b0) |=> (add_overflow_flag == 1'b0)
    );

    // Loading a zero into the register forces the next sampled output low.
    check_load_zero_clears_output_next_cycle: assert property (
        @(posedge CLK) disable iff (!AR[0])
        ((E[0] == 1'b1) && (O[0] == 1'b0)) |=> (add_overflow_flag == 1'b0)
    );

endmodule