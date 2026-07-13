module main_sva (
    input logic [2:0] val1,
    input logic [2:0] val2,
    input logic [2:0] result
);
    // Result matches the exact ternary expression in RTL.
    check_function_equivalence: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            result == ((val1 == val2) ? (val1 << 1) :
                      (val1 == 3'd0) ? 3'd0 :
                      (val1 == 3'd1) ? 3'd1 :
                      (val1 == 3'd2) ? 3'd2 :
                      (val1 == 3'd3) ? 3'd4 : 3'd4)
    );

    // When val1 equals val2, result is val1 shifted left by 1.
    check_equal_shift: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            (val1 == val2) |-> (result == (val1 << 1))
    );

    // When val1 equals val2, LSB of result is zero (left shift property).
    check_equal_lsb_zero: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            (val1 == val2) |-> (result[0] == 1'b0)
    );

    // When val1 != val2 and val1 == 0, result is 0.
    check_neq_val1_0: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 != val2) && (val1 == 3'd0)) |-> (result == 3'd0)
    );

    // When val1 != val2 and val1 == 1, result is 1.
    check_neq_val1_1: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 != val2) && (val1 == 3'd1)) |-> (result == 3'd1)
    );

    // When val1 != val2 and val1 == 2, result is 2.
    check_neq_val1_2: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 != val2) && (val1 == 3'd2)) |-> (result == 3'd2)
    );

    // When val1 != val2 and val1 == 3, result is 4.
    check_neq_val1_3: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 != val2) && (val1 == 3'd3)) |-> (result == 3'd4)
    );

    // When val1 != val2 and val1 >= 4, result is 4.
    check_neq_val1_ge4: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 != val2) && (val1 >= 3'd4)) |-> (result == 3'd4)
    );

    // When val1 != val2, result is restricted to {0,1,2,4}.
    check_neq_allowed_values: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            (val1 != val2) |-> (result inside {3'd0,3'd1,3'd2,3'd4})
    );

    // Example: when equal and val1==3, result is 6 (3<<1 in 3-bit width).
    check_equal_example_val1_3: assert property (
        @(posedge val1[0] or posedge val1[1] or posedge val1[2] or posedge val2[0] or posedge val2[1] or posedge val2[2])
            ((val1 == val2) && (val1 == 3'd3)) |-> (result == 3'd6)
    );
endmodule