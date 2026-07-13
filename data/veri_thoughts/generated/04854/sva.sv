module counter_register_sva (
    input logic       clk,
    input logic       reset,
    input logic [7:0] data,
    input logic       select,
    input logic [7:0] sum,
    input logic [3:0] counter,
    input logic [7:0] register
);

    // Synchronous reset clears all state on the next clock.
    check_reset_clears_state: assert property (
        @(posedge clk)
        reset |=> (counter == 4'h0) && (register == 8'h00) && (sum == 8'h00)
    );

    // A selected cycle loads the register from data.
    check_select_loads_register: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && select) |-> (register == $past(data))
    );

    // A selected cycle leaves the counter unchanged.
    check_select_holds_counter: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && select) |-> (counter == $past(counter))
    );

    // A selected cycle updates sum from the prior register and counter.
    check_select_sum_uses_prior_state: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && select) |-> (sum == ($past(register) + {4'b0000, $past(counter)}))
    );

    // A count cycle increments the counter by one.
    check_count_increments_counter: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && !select) |-> (counter == ($past(counter) + 4'h1))
    );

    // A count cycle leaves the register unchanged.
    check_count_holds_register: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && !select) |-> (register == $past(register))
    );

    // A count cycle updates sum from the prior register and counter.
    check_count_sum_uses_prior_state: assert property (
        @(posedge clk) disable iff (reset || $initstate)
        $past(!reset && !select) |-> (sum == ($past(register) + {4'b0000, $past(counter)}))
    );

endmodule

bind counter_register counter_register_sva counter_register_sva_inst (
    .clk(clk),
    .reset(reset),
    .data(data),
    .select(select),
    .sum(sum),
    .counter(counter),
    .register(register)
);