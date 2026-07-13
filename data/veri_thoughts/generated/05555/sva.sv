module my_or2_sva (
    input logic clk,
    input logic o,
    input logic i0,
    input logic i1
);

    // Output equals the OR of the two inputs.
    check_or_function: assert property (
        @(posedge clk) o == (i0 | i1)
    );

    // Output is low when both inputs are low.
    check_both_inputs_low: assert property (
        @(posedge clk) (!i0 && !i1) |-> !o
    );

    // Output is high whenever i0 is high.
    check_i0_high_sets_output: assert property (
        @(posedge clk) i0 |-> o
    );

    // Output is high whenever i1 is high.
    check_i1_high_sets_output: assert property (
        @(posedge clk) i1 |-> o
    );

endmodule