module dynamic_gate_sva (
    input logic in,
    input logic clk,
    input logic out
);

    // out must be high on the first clock after a high input.
    check_out_high_after_high_input: assert property (
        @(posedge clk) in |=> (out == 1'b1)
    );

    // out must be low on the first clock after a low input.
    check_out_low_after_low_input: assert property (
        @(posedge clk) !in |=> (out == 1'b0)
    );

    // out must be high on the second clock after a high input.
    check_out_high_two_cycles_after_high_input: assert property (
        @(posedge clk) in |=> ##1 (out == 1'b1)
    );

    // out must be low on the second clock after a low input.
    check_out_low_two_cycles_after_low_input: assert property (
        @(posedge clk) !in |=> ##1 (out == 1'b0)
    );

endmodule