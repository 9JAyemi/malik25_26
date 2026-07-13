module shift_register_sva (
    input logic clk,
    input logic d,
    input logic q,
    input logic [2:0] reg_array
);

    // q directly mirrors reg_array[0] via continuous assignment.
    check_q_mirrors_reg0: assert property (
        @(posedge clk) q == reg_array[0]
    );

    // On each clock, reg_array shifts left and captures d on bit[2].
    check_shift_update_vector: assert property (
        @(posedge clk) reg_array == { $past(reg_array[1:0]), $past(d) }
    );

    // Bit[0] updates from previous bit[1].
    check_bit0_from_bit1: assert property (
        @(posedge clk) reg_array[0] == $past(reg_array[1])
    );

    // Bit[1] updates from previous bit[2].
    check_bit1_from_bit2: assert property (
        @(posedge clk) reg_array[1] == $past(reg_array[2])
    );

    // Bit[2] captures previous d.
    check_bit2_from_d: assert property (
        @(posedge clk) reg_array[2] == $past(d)
    );

    // q equals d delayed by two cycles (guarded against insufficient history).
    check_q_two_cycle_delay_of_d: assert property (
        @(posedge clk) !$isunknown($past(d,2)) |-> (q == $past(d,2))
    );

endmodule