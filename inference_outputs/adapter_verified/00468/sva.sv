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

// When disabled, data_out is forced low on the next clock.
    check_clear_when_disabled: assert property (
        @(posedge clk) !en |=> (data_out == 1'b0)
    );

// data_out is always either the previous cycle's data_in or 0.
    check_next_value_is_previous_input_or_zero: assert property (
        @(posedge clk) 1'b1 |=> ((data_out == $past(data_in)) || (data_out == 1'b0))
    );

// If data_in is 0 and enabled, data_out becomes 0 on the next clock.
    check_zero_input_sets_zero_when_enabled: assert property (
        @(posedge clk) (en && (data_in == 1'b0)) |=> (data_out == 1'b0)
    );

// If data_in is 1 and enabled, data_out becomes 1 on the next clock.
    check_one_input_sets_one_when_enabled: assert property (
        @(posedge clk) (en && (data_in == 1'b1)) |=> (data_out == 1'b1)
    );

endmodule
