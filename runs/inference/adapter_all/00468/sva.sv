module clock_gate_en_sva (
    input logic clk,
    input logic en,
    input logic data_in,
    input logic data_out
);

    // When enabled, data_out captures data_in on the next clock.
    check_capture_when_enabled: assert property (
        @(posedge clk) en |=> (data_out == $past(data_in))
    );

    // When disabled, data_out clears on the next clock.
    check_clear_when_disabled: assert property (
        @(posedge clk) !en |=> (data_out == 1'b0)
    );

    // data_out always matches the previous cycle's enable and data_in value.
    check_registered_function: assert property (
        @(posedge clk) 1'b1 |=> (data_out == ($past(en) ? $past(data_in) : 1'b0))
    );

endmodule