module clock_gate_en_sva (
    input logic clk,
    input logic en,
    input logic data_in,
    input logic data_out
);

    // When enabled, the next-cycle output matches the sampled input.
    check_capture_when_enabled: assert property (
        @(posedge clk) en |=> (data_out == $past(data_in))
    );

    // When disabled, the next-cycle output is forced low.
    check_drive_low_when_disabled: assert property (
        @(posedge clk) !en |=> (data_out == 1'b0)
    );

    // Each cycle, the output follows the prior-cycle enable/data function.
    check_registered_output_function: assert property (
        @(posedge clk) 1'b1 |=> (data_out == ($past(en) ? $past(data_in) : 1'b0))
    );

endmodule