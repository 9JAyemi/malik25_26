module compare_and_concatenate_sva (
    input logic CLK,
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [15:0] c
);
    // c matches exact concatenation: {abs(a-b), min(a,b)}
    check_exact_concat: assert property (
        @(posedge CLK) c == { ((a >= b) ? (a - b) : (b - a)), ((a >= b) ? b : a) }
    );

    // When a >= b, upper byte equals a - b
    check_upper_when_ge: assert property (
        @(posedge CLK) (a >= b) |-> (c[15:8] == (a - b))
    );

    // When a >= b, lower byte equals b
    check_lower_when_ge: assert property (
        @(posedge CLK) (a >= b) |-> (c[7:0] == b)
    );

    // When a < b, upper byte equals b - a
    check_upper_when_lt: assert property (
        @(posedge CLK) (a < b) |-> (c[15:8] == (b - a))
    );

    // When a < b, lower byte equals a
    check_lower_when_lt: assert property (
        @(posedge CLK) (a < b) |-> (c[7:0] == a)
    );

    // If a == b, upper byte is 0 and lower byte equals a
    check_zero_when_equal: assert property (
        @(posedge CLK) (a == b) |-> (c == {8'h00, a})
    );

    // Lower byte equals one of the inputs (min(a,b))
    check_lower_is_input: assert property (
        @(posedge CLK) (c[7:0] == a) || (c[7:0] == b)
    );

    // Lower byte is less than or equal to both inputs
    check_lower_is_min_inequality: assert property (
        @(posedge CLK) (c[7:0] <= a) && (c[7:0] <= b)
    );

    // Upper byte equals absolute difference |a - b|
    check_upper_is_absdiff: assert property (
        @(posedge CLK) c[15:8] == ((a >= b) ? (a - b) : (b - a))
    );

    // Sum of upper and lower bytes equals max(a,b)
    check_sum_equals_max: assert property (
        @(posedge CLK) (c[15:8] + c[7:0]) == ((a >= b) ? a : b)
    );
endmodule