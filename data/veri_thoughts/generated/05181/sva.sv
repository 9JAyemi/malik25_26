module Coun_Baud_sva #(parameter N = 10, M = 656) (
    input logic clk,
    input logic reset,
    input logic max_tick,
    input logic [N-1:0] r_reg,
    input logic [N-1:0] r_next
);

    // r_next matches the RTL next-state equation.
    check_r_next_definition: assert property (
        @(posedge clk) disable iff (reset)
        r_next == ((r_reg == (M-1)) ? '0 : (r_reg + 1'b1))
    );

    // max_tick reflects the terminal-count decode.
    check_max_tick_definition: assert property (
        @(posedge clk) disable iff (reset)
        max_tick == ((r_reg == (M-1)) ? 1'b1 : 1'b0)
    );

    // The counter register loads the prior cycle's r_next value.
    check_r_reg_loads_r_next: assert property (
        @(posedge clk) disable iff (reset)
        1'b1 |=> (r_reg == $past(r_next))
    );

    // A terminal count wraps the counter to zero on the next clock.
    check_terminal_wrap: assert property (
        @(posedge clk) disable iff (reset)
        (r_reg == (M-1)) |=> (r_reg == '0)
    );

    // A non-terminal count advances by one on the next clock.
    check_nonterminal_increment: assert property (
        @(posedge clk) disable iff (reset)
        (r_reg != (M-1)) |=> (r_reg == ($past(r_reg) + 1'b1))
    );

    generate
        if (M > 1) begin : gen_m_gt_1
            // max_tick is a one-cycle pulse when M is greater than one.
            check_max_tick_single_cycle: assert property (
                @(posedge clk) disable iff (reset)
                max_tick |=> !max_tick
            );

            // The count just before terminal count produces max_tick next cycle.
            check_preterminal_sets_max_tick: assert property (
                @(posedge clk) disable iff (reset)
                (r_reg == (M-2)) |=> max_tick
            );
        end
    endgenerate

endmodule