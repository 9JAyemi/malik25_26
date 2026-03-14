module half_adder_nand_sva (
    input logic clk,
    input logic a,
    input logic b,
    input logic sum,
    input logic cout
);
    // Sum equals (~a | b).
    check_sum_function: assert property (
        @(posedge clk) disable iff (1'b0) sum == ((~a) | b)
    );

    // Cout equals (a | ~b).
    check_cout_function: assert property (
        @(posedge clk) disable iff (1'b0) cout == (a | (~b))
    );

    // At least one output is HIGH at all times.
    check_sum_or_cout_one: assert property (
        @(posedge clk) disable iff (1'b0) (sum | cout) == 1'b1
    );

    // Output XOR equals input XOR.
    check_xor_relation: assert property (
        @(posedge clk) disable iff (1'b0) (sum ^ cout) == (a ^ b)
    );

    // For a=0,b=0 -> sum=1, cout=1.
    check_tt_00: assert property (
        @(posedge clk) disable iff (1'b0) (!a && !b) |-> (sum && cout)
    );

    // For a=0,b=1 -> sum=1, cout=0.
    check_tt_01: assert property (
        @(posedge clk) disable iff (1'b0) (!a && b) |-> (sum && !cout)
    );

    // For a=1,b=0 -> sum=0, cout=1.
    check_tt_10: assert property (
        @(posedge clk) disable iff (1'b0) (a && !b) |-> (!sum && cout)
    );

    // For a=1,b=1 -> sum=1, cout=1.
    check_tt_11: assert property (
        @(posedge clk) disable iff (1'b0) (a && b) |-> (sum && cout)
    );

    // Sum is LOW only when a=1 and b=0.
    check_sum_zero_only_on_10: assert property (
        @(posedge clk) disable iff (1'b0) (sum == 1'b0) |-> (a && !b)
    );

    // Cout is LOW only when a=0 and b=1.
    check_cout_zero_only_on_01: assert property (
        @(posedge clk) disable iff (1'b0) (cout == 1'b0) |-> (!a && b)
    );
endmodule