module shift_and_sum_sva (
    input logic       clk,
    input logic       up_down,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [7:0] out,
    input logic [3:0] counter1_out,
    input logic [3:0] counter2_out,
    input logic [3:0] binary_adder_out
);

    // counter1 increments by one when up_down is high.
    check_counter1_counts_up: assert property (
        @(posedge clk) up_down |=> counter1_out == $past(counter1_out) + 4'd1
    );

    // counter1 decrements by one when up_down is low.
    check_counter1_counts_down: assert property (
        @(posedge clk) !up_down |=> counter1_out == $past(counter1_out) - 4'd1
    );

    // counter2 increments by one when up_down is high.
    check_counter2_counts_up: assert property (
        @(posedge clk) up_down |=> counter2_out == $past(counter2_out) + 4'd1
    );

    // counter2 decrements by one when up_down is low.
    check_counter2_counts_down: assert property (
        @(posedge clk) !up_down |=> counter2_out == $past(counter2_out) - 4'd1
    );

    // adder output matches the sum of the two counters.
    check_adder_sum: assert property (
        @(posedge clk) binary_adder_out == (counter1_out + counter2_out)
    );

    // output lower nibble matches the adder result.
    check_out_lower_matches_adder: assert property (
        @(posedge clk) out[3:0] == binary_adder_out
    );

    // output upper nibble matches A shifted right by B.
    check_out_upper_matches_shift: assert property (
        @(posedge clk) out[7:4] == (A >> B)
    );

    // adder result increases by two when counting up.
    check_adder_counts_up_by_two: assert property (
        @(posedge clk) up_down |=> binary_adder_out == $past(binary_adder_out) + 4'd2
    );

    // adder result decreases by two when counting down.
    check_adder_counts_down_by_two: assert property (
        @(posedge clk) !up_down |=> binary_adder_out == $past(binary_adder_out) - 4'd2
    );

endmodule