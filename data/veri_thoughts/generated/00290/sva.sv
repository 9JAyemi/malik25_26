module top_module_sva (
    input logic clk,
    input logic reset,
    input logic [7:0] d1,
    input logic [7:0] d2,
    input logic select,
    input logic [7:0] q_active,
    input logic [15:0] result,
    input logic [7:0] reg1,
    input logic [7:0] reg2,
    input logic [3:0] counter
);

    // Reset loads the implemented register and counter values.
    check_reset_loads_state: assert property (
        @(posedge clk) reset |=> (reg1 == 8'h34) && (reg2 == 8'h34) && (counter == 4'h0)
    );

    // Reset also produces the expected concatenated result value.
    check_reset_sets_result: assert property (
        @(posedge clk) reset |=> (result == 16'h3434)
    );

    // The result output is just the concatenation of reg1 and reg2.
    check_result_matches_registers: assert property (
        @(posedge clk) disable iff (reset) result == {reg1, reg2}
    );

    // With select high, q_active reflects reg1.
    check_q_active_when_select_high: assert property (
        @(posedge clk) disable iff (reset) (select == 1'b1) |-> (q_active == reg1)
    );

    // With select low, q_active reflects the zero-extended counter.
    check_q_active_when_select_low: assert property (
        @(posedge clk) disable iff (reset) (select == 1'b0) |-> (q_active == {4'h0, counter})
    );

    // A high select causes reg1 to load d1 on the next cycle.
    check_reg1_loads_d1_when_selected: assert property (
        @(posedge clk) disable iff (reset) (select == 1'b1) |=> (reg1 == $past(d1))
    );

    // A low select leaves reg1 unchanged.
    check_reg1_holds_when_select_low: assert property (
        @(posedge clk) disable iff (reset) (select == 1'b0) |=> $stable(reg1)
    );

    // reg2 never changes outside reset.
    check_reg2_stable_without_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset) |=> $stable(reg2)
    );

    // The counter never changes outside reset.
    check_counter_stable_without_reset: assert property (
        @(posedge clk) disable iff (reset) (!reset) |=> $stable(counter)
    );

    // When selected, q_active matches the upper byte of result through reg1.
    check_q_active_matches_result_upper_when_selected: assert property (
        @(posedge clk) disable iff (reset) (select == 1'b1) |-> (q_active == result[15:8])
    );

endmodule