module debounce_switch_sva #(
    parameter WIDTH = 1,
    parameter N = 3,
    parameter RATE = 125000
) (
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] in,
    input logic [WIDTH-1:0] out,
    input logic [23:0] cnt_reg,
    input logic [N-1:0] debounce_reg [WIDTH-1:0],
    input logic [WIDTH-1:0] state
);

    // clk is the only clock; rst is an active-high asynchronous reset.
    // The logic is sequential with combinational out = state.

    // Reset forces the counter low.
    check_reset_clears_counter: assert property (
        @(posedge clk) rst |-> (cnt_reg == 24'd0)
    );

    // Reset forces the debounced state and output low.
    check_reset_clears_state_and_out: assert property (
        @(posedge clk) rst |-> (state == {WIDTH{1'b0}}) && (out == {WIDTH{1'b0}})
    );

    // Output always mirrors the internal state.
    check_out_matches_state: assert property (
        @(posedge clk) disable iff (rst) (out == state)
    );

    // Counter increments while below RATE.
    check_counter_increments_below_rate: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(!rst) && ($past(cnt_reg) < RATE)) |-> (cnt_reg == ($past(cnt_reg) + 24'd1))
    );

    // Counter wraps to zero when RATE is reached or exceeded.
    check_counter_wraps_at_rate: assert property (
        @(posedge clk) disable iff (rst || $initstate)
        ($past(!rst) && !($past(cnt_reg) < RATE)) |-> (cnt_reg == 24'd0)
    );

    genvar i;
    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_bit_checks

            // Reset clears each debounce history register.
            check_reset_clears_debounce: assert property (
                @(posedge clk) rst |-> (debounce_reg[i] == {N{1'b0}})
            );

            // Debounce history holds when the sample counter is not zero.
            check_debounce_holds_without_sample: assert property (
                @(posedge clk) disable iff (rst || $initstate)
                ($past(!rst) && ($past(cnt_reg) != 24'd0)) |-> (debounce_reg[i] == $past(debounce_reg[i]))
            );

            if (N > 1) begin : gen_shift_multi
                // Debounce history shifts in the input when the sample counter is zero.
                check_debounce_shifts_on_sample: assert property (
                    @(posedge clk) disable iff (rst || $initstate)
                    ($past(!rst) && ($past(cnt_reg) == 24'd0)) |-> (debounce_reg[i] == { $past(debounce_reg[i][N-2:0]), $past(in[i]) })
                );
            end else begin : gen_shift_single
                // Single-bit debounce history captures the input when sampled.
                check_debounce_captures_on_sample: assert property (
                    @(posedge clk) disable iff (rst || $initstate)
                    ($past(!rst) && ($past(cnt_reg) == 24'd0)) |-> (debounce_reg[i] == $past(in[i]))
                );
            end

            // State clears when the previous debounce history is all zero.
            check_state_clears_on_all_zero_history: assert property (
                @(posedge clk) disable iff (rst || $initstate)
                ($past(!rst) && (~|$past(debounce_reg[i]))) |-> (state[i] == 1'b0)
            );

            // State sets when the previous debounce history is all one.
            check_state_sets_on_all_one_history: assert property (
                @(posedge clk) disable iff (rst || $initstate)
                ($past(!rst) && (&$past(debounce_reg[i]))) |-> (state[i] == 1'b1)
            );

            // State holds when the previous debounce history is mixed.
            check_state_holds_on_mixed_history: assert property (
                @(posedge clk) disable iff (rst || $initstate)
                ($past(!rst) && !(~|$past(debounce_reg[i])) && !(&$past(debounce_reg[i]))) |-> (state[i] == $past(state[i]))
            );

        end
    endgenerate

endmodule