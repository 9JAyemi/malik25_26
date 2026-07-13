module debounce_switch_sva #(
    parameter int WIDTH = 1,
    parameter int N = 3,
    parameter int RATE = 125000
)(
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] in,
    input logic [WIDTH-1:0] out,
    input logic [23:0] cnt_reg,
    input logic [N-1:0] debounce_reg [WIDTH-1:0],
    input logic [WIDTH-1:0] state
);

    // Reset clears the counter, state, and output on the next clock.
    check_reset_clears_main_regs: assert property (
        @(posedge clk) rst |=> (cnt_reg == 24'd0) && (state == {WIDTH{1'b0}}) && (out == {WIDTH{1'b0}})
    );

    // The counter increments while it is below RATE.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (rst)
        (cnt_reg < RATE) |=> (cnt_reg == $past(cnt_reg) + 24'd1)
    );

    // The counter wraps to zero when it is not below RATE.
    check_counter_wraps_to_zero: assert property (
        @(posedge clk) disable iff (rst)
        (!(cnt_reg < RATE)) |=> (cnt_reg == 24'd0)
    );

    // The output always mirrors the internal state register.
    check_output_matches_state: assert property (
        @(posedge clk) disable iff (rst)
        (out == state)
    );

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_bit_asserts

            // Reset clears each debounce shift register.
            check_reset_clears_debounce: assert property (
                @(posedge clk) rst |=> (debounce_reg[i] == {N{1'b0}})
            );

            // A sample is shifted in only when the counter is zero.
            check_debounce_shifts_on_sample: assert property (
                @(posedge clk) disable iff (rst)
                (cnt_reg == 24'd0) |=> (debounce_reg[i] == {$past(debounce_reg[i][N-2:0]), $past(in[i])})
            );

            // The debounce shift register holds between sample points.
            check_debounce_holds_between_samples: assert property (
                @(posedge clk) disable iff (rst)
                (cnt_reg != 24'd0) |=> (debounce_reg[i] == $past(debounce_reg[i]))
            );

            // State clears when the sampled history is all zeros.
            check_state_clears_on_all_zero_history: assert property (
                @(posedge clk) disable iff (rst)
                (debounce_reg[i] == {N{1'b0}}) |=> (state[i] == 1'b0)
            );

            // State sets when the sampled history is all ones.
            check_state_sets_on_all_one_history: assert property (
                @(posedge clk) disable iff (rst)
                (debounce_reg[i] == {N{1'b1}}) |=> (state[i] == 1'b1)
            );

            // State holds when the sampled history is mixed.
            check_state_holds_on_mixed_history: assert property (
                @(posedge clk) disable iff (rst)
                ((debounce_reg[i] != {N{1'b0}}) && (debounce_reg[i] != {N{1'b1}})) |=> (state[i] == $past(state[i]))
            );

        end
    endgenerate

endmodule