module gray_code_state_machine_sva #(parameter n = 4) (
    input logic clk,
    input logic rst,
    input logic [n-1:0] out
);

    // Output stays within the values produced by the case mapping.
    check_out_valid_range: assert property (
        @(posedge clk) disable iff (rst)
        (out <= 7)
    );

    // A reset seen on the prior clock forces the output to zero.
    check_reset_clears_output: assert property (
        @(posedge clk) disable iff (rst)
        ($past(rst) === 1'b1) |-> (out == '0)
    );

    // Output 0 is a stable fixed point.
    check_out_zero_stays_zero: assert property (
        @(posedge clk) disable iff (rst)
        (out == '0) |=> (out == '0)
    );

    // Output 1 is a stable fixed point.
    check_out_one_stays_one: assert property (
        @(posedge clk) disable iff (rst)
        (out == 1) |=> (out == 1)
    );

    // Output 2 must transition to 3 on the next cycle.
    check_out_two_to_three: assert property (
        @(posedge clk) disable iff (rst)
        (out == 2) |=> (out == 3)
    );

    // Output 3 must transition to 2 on the next cycle.
    check_out_three_to_two: assert property (
        @(posedge clk) disable iff (rst)
        (out == 3) |=> (out == 2)
    );

    // Output 4 must transition to 6 on the next cycle.
    check_out_four_to_six: assert property (
        @(posedge clk) disable iff (rst)
        (out == 4) |=> (out == 6)
    );

    // Output 5 must transition to 7 on the next cycle.
    check_out_five_to_seven: assert property (
        @(posedge clk) disable iff (rst)
        (out == 5) |=> (out == 7)
    );

    // Output 6 must transition to 5 on the next cycle.
    check_out_six_to_five: assert property (
        @(posedge clk) disable iff (rst)
        (out == 6) |=> (out == 5)
    );

    // Output 7 must transition to 4 on the next cycle.
    check_out_seven_to_four: assert property (
        @(posedge clk) disable iff (rst)
        (out == 7) |=> (out == 4)
    );

endmodule