module debounce_switch_sva #(
    parameter WIDTH = 1,
    parameter N = 3,
    parameter RATE = 125000
)(
    input logic clk,
    input logic rst,
    input logic [WIDTH-1:0] in,
    input logic [WIDTH-1:0] out,
    input logic [23:0] cnt_reg,
    input logic [N-1:0] debounce_reg [WIDTH-1:0],
    input logic [WIDTH-1:0] state
);

    // Clock: clk
    // Reset: rst is active-high and asynchronous in the RTL
    // Logic: sequential counter/state with combinational out = state

    genvar i;

    // Output always mirrors the internal state register.
    check_out_matches_state: assert property (
        @(posedge clk) disable iff (rst)
        out == state
    );

    // Reset clears the counter.
    check_reset_clears_counter: assert property (
        @(posedge clk)
        rst |-> (cnt_reg == 24'd0)
    );

    // Reset clears the state register.
    check_reset_clears_state: assert property (
        @(posedge clk)
        rst |-> (state == {WIDTH{1'b0}})
    );

    // Reset drives the output low.
    check_reset_clears_output: assert property (
        @(posedge clk)
        rst |-> (out == {WIDTH{1'b0}})
    );

    // Counter increments while it is below RATE.
    check_counter_increments: assert property (
        @(posedge clk) disable iff (rst)
        (cnt_reg < RATE) |=> (cnt_reg == ($past(cnt_reg) + 24'd1))
    );

    // Counter wraps to zero when it is not below RATE.
    check_counter_wraps: assert property (
        @(posedge clk) disable iff (rst)
        !(cnt_reg < RATE) |=> (cnt_reg == 24'd0)
    );

    generate
        for (i = 0; i < WIDTH; i = i + 1) begin : gen_width_checks

            // Reset clears each debounce history register.
            check_reset_clears_debounce: assert property (
                @(posedge clk)
                rst |-> (debounce_reg[i] == {N{1'b0}})
            );

            if (N > 1) begin : gen_n_gt_1
                // On a sample tick, the debounce history shifts in the input bit.
                check_debounce_shifts_on_tick: assert property (
                    @(posedge clk) disable iff (rst)
                    (cnt_reg == 24'd0) |=> (debounce_reg[i] == {$past(debounce_reg[i][N-2:0]), $past(in[i])})
                );
            end else begin : gen_n_eq_1
                // On a sample tick, the debounce history captures the input bit.
                check_debounce_captures_on_tick: assert property (
                    @(posedge clk) disable iff (rst)
                    (cnt_reg == 24'd0) |=> (debounce_reg[i] == $past(in[i]))
                );
            end

            // Between sample ticks, the debounce history holds.
            check_debounce_holds_between_ticks: assert property (
                @(posedge clk) disable iff (rst)
                (cnt_reg != 24'd0) |=> (debounce_reg[i] == $past(debounce_reg[i]))
            );

            // All-zero history clears the corresponding state bit.
            check_state_clears_on_zero_history: assert property (
                @(posedge clk) disable iff (rst)
                (debounce_reg[i] == {N{1'b0}}) |=> (state[i] == 1'b0)
            );

            // All-one history sets the corresponding state bit.
            check_state_sets_on_one_history: assert property (
                @(posedge clk) disable iff (rst)
                (debounce_reg[i] == {N{1'b1}}) |=> (state[i] == 1'b1)
            );

            // Mixed history preserves the corresponding state bit.
            check_state_holds_on_mixed_history: assert property (
                @(posedge clk) disable iff (rst)
                ((debounce_reg[i] != {N{1'b0}}) && (debounce_reg[i] != {N{1'b1}})) |=> (state[i] == $past(state[i]))
            );

        end
    endgenerate

endmodule