module debounce_switch_sva #(
    parameter WIDTH = 1,
    parameter N     = 3,
    parameter RATE  = 125000
)(
    input  logic                  clk,
    input  logic                  rst,
    input  logic [WIDTH-1:0]      in,
    input  logic [WIDTH-1:0]      out,
    // Internal signals from DUT (connect via bind)
    input  logic [23:0]           cnt_reg,
    input  logic [N-1:0]          debounce_reg [WIDTH-1:0],
    input  logic [WIDTH-1:0]      state
);

    ///// Reset behavior /////
    // After a reset cycle, counter and state are 0 on the next cycle.
    reset_clears_counter_state: assert property (
        @(posedge clk) disable iff (rst)
            $past(rst) |-> (cnt_reg == 24'd0) && (state == '0)
    );

    genvar gi_rst;
    generate
        for (gi_rst = 0; gi_rst < WIDTH; gi_rst++) begin : GEN_RESET_DB
            // After a reset cycle, each debounce shift register is 0 on the next cycle.
            reset_clears_debounce_regs: assert property (
                @(posedge clk) disable iff (rst)
                    $past(rst) |-> (debounce_reg[gi_rst] == '0)
            );
        end
    endgenerate

    ///// Counter behavior /////
    // Counter value is always within 0..RATE when not in reset.
    counter_within_range: assert property (
        @(posedge clk) disable iff (rst)
            (cnt_reg <= RATE)
    );

    // If previous cnt_reg < RATE, it increments by 1.
    counter_increments_below_RATE: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && $past(cnt_reg < RATE)) |-> (cnt_reg == $past(cnt_reg) + 24'd1)
    );

    // If previous cnt_reg >= RATE, it wraps to 0.
    counter_wraps_at_RATE: assert property (
        @(posedge clk) disable iff (rst)
            ($past(!rst) && $past(cnt_reg >= RATE)) |-> (cnt_reg == 24'd0)
    );

    ///// Output wiring /////
    // out mirrors internal state.
    out_mirrors_state: assert property (
        @(posedge clk) disable iff (rst)
            (out == state)
    );

    ///// Debounce sampling and state update /////
    genvar i;
    generate
        for (i = 0; i < WIDTH; i++) begin : GEN_DEBOUNCE
            // On a sampling cycle (prev cnt_reg==0), debounce_reg shifts in in[i].
            debounce_shifts_on_sample: assert property (
                @(posedge clk) disable iff (rst)
                    ($past(!rst) && $past(cnt_reg == 24'd0))
                    |-> (debounce_reg[i] == {$past(debounce_reg[i][N-2:0]), $past(in[i])})
            );

            // When not sampling (prev cnt_reg!=0), debounce_reg holds its value.
            debounce_holds_when_not_sampling: assert property (
                @(posedge clk) disable iff (rst)
                    ($past(!rst) && $past(cnt_reg != 24'd0))
                    |-> (debounce_reg[i] == $past(debounce_reg[i]))
            );

            // If previous debounce_reg was all 0s, state[i] becomes 0.
            state_sets_low_when_all_zero: assert property (
                @(posedge clk) disable iff (rst)
                    ($past(!rst) && ($past(|debounce_reg[i]) == 1'b0))
                    |-> (state[i] == 1'b0)
            );

            // If previous debounce_reg was all 1s, state[i] becomes 1.
            state_sets_high_when_all_one: assert property (
                @(posedge clk) disable iff (rst)
                    ($past(!rst) && ($past(&debounce_reg[i]) == 1'b1))
                    |-> (state[i] == 1'b1)
            );

            // If previous debounce_reg was mixed (not all 0s or 1s), state[i] holds.
            state_holds_when_reg_mixed: assert property (
                @(posedge clk) disable iff (rst)
                    ($past(!rst) && ($past(|debounce_reg[i]) == 1'b1) && ($past(&debounce_reg[i]) == 1'b0))
                    |-> (state[i] == $past(state[i]))
            );
        end
    endgenerate

endmodule