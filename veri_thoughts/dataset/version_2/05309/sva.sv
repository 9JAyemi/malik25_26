module adder_subtractor_sva (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       control,
    input logic [3:0] out
);

    // No clock or reset exists in the RTL; sample on the formal global clock.

    // When control is high, out must equal the 4-bit sum of a and b.
    check_add_path_result: assert property (
        @($global_clock) control |-> (out == (a + b))
    );

    // When control is low, out must equal the 4-bit difference of a and b.
    check_subtract_path_result: assert property (
        @($global_clock) !control |-> (out == (a - b))
    );

endmodule