module max_value_sva (
    input logic clk,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] max
);

    // When A is greater than B, max must be A.
    check_max_selects_a: assert property (
        @(posedge clk) (A > B) |-> (max == A)
    );

    // When B is greater than A, max must be B.
    check_max_selects_b: assert property (
        @(posedge clk) (B > A) |-> (max == B)
    );

    // When A and B are equal, max must be zero.
    check_equal_inputs_drive_zero: assert property (
        @(posedge clk) (A == B) |-> (max == 8'h00)
    );

    // A zero max output can only occur when the inputs are equal.
    check_zero_only_on_equal_inputs: assert property (
        @(posedge clk) (max == 8'h00) |-> (A == B)
    );

    // max must match the full RTL comparison function.
    check_full_max_function: assert property (
        @(posedge clk) max == ((A > B) ? A : ((B > A) ? B : 8'h00))
    );

endmodule