module debouncer_sva #(
    parameter int clk_freq = 100000,
    parameter int debounce_time = 10
) (
    input logic clk,
    input logic in,
    input logic out,
    input logic [1:0] state,
    input logic [31:0] debounce_count
);

    localparam logic [1:0] STABLE  = 2'b00;
    localparam logic [1:0] UNSTABLE = 2'b01;
    localparam logic [1:0] DEBOUNCE = 2'b10;

    // Stable state holds when the input matches the output.
    check_stable_holds_when_input_matches_output: assert property (
        @(posedge clk) (state == STABLE && in == out) |=> (state == STABLE && out == in)
    );

    // Stable state detects an input change and enters unstable.
    check_stable_changes_on_input_mismatch: assert property (
        @(posedge clk) (state == STABLE && in != out) |=> (state == UNSTABLE && out == $past(out))
    );

    // Unstable state decrements the debounce counter when it is nonzero.
    check_unstable_counts_down_when_nonzero: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count != 0) |=> (state == UNSTABLE && debounce_count == ($past(debounce_count) - 32'd1))
    );

    // Unstable state holds the output when the debounce counter is nonzero.
    check_unstable_holds_output_when_count_nonzero: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count != 0) |=> (out == $past(out))
    );

    // Unstable state clears the counter and enters debounce when it reaches zero.
    check_unstable_clears_count_and_enters_debounce: assert property (
        @(posedge clk) (state == UNSTABLE && debounce_count == 0) |=> (state == DEBOUNCE && debounce_count == 0 && out == $past(in))
    );

    // Debounce state holds the output when the input matches the output.
    check_debounce_holds_output_when_input_matches_output: assert property (
        @(posedge clk) (state == DEBOUNCE && in == out) |=> (state == STABLE && out == $past(out))
    );

    // Debounce state detects an input change and returns to unstable.
    check_debounce_changes_on_input_mismatch: assert property (
        @(posedge clk) (state == DEBOUNCE && in != out) |=> (state == UNSTABLE && debounce_count == ($past(debounce_count) - 32'd1) && out == $past(out))
    );

endmodule