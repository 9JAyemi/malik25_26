module adder_sva (
    input logic       clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic       cin,
    input logic [3:0] sum,
    input logic       cout
);

    // Combined output matches 4-bit addition with carry-in.
    check_arithmetic_result: assert property (
        @(posedge clk)
        {cout, sum} == ({1'b0, a} + {1'b0, b} + {4'b0000, cin})
    );

    // Sum bit 0 follows the first full-adder XOR equation.
    check_sum_bit0: assert property (
        @(posedge clk)
        sum[0] == (a[0] ^ b[0] ^ cin)
    );

    // Sum bit 1 uses the carry from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk)
        sum[1] == (
            a[1] ^ b[1] ^
            ((a[0] & b[0]) | (cin & (a[0] ^ b[0])))
        )
    );

    // Sum bit 2 uses the carry from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk)
        sum[2] == (
            a[2] ^ b[2] ^
            (
                (a[1] & b[1]) |
                (
                    ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) &
                    (a[1] ^ b[1])
                )
            )
        )
    );

    // Sum bit 3 uses the carry from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk)
        sum[3] == (
            a[3] ^ b[3] ^
            (
                (a[2] & b[2]) |
                (
                    (
                        (a[1] & b[1]) |
                        (
                            ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) &
                            (a[1] ^ b[1])
                        )
                    ) &
                    (a[2] ^ b[2])
                )
            )
        )
    );

    // Carry-out follows the final full-adder carry equation.
    check_cout_equation: assert property (
        @(posedge clk)
        cout == (
            (a[3] & b[3]) |
            (
                (
                    (a[2] & b[2]) |
                    (
                        (
                            (a[1] & b[1]) |
                            (
                                ((a[0] & b[0]) | (cin & (a[0] ^ b[0]))) &
                                (a[1] ^ b[1])
                            )
                        ) &
                        (a[2] ^ b[2])
                    )
                ) &
                (a[3] ^ b[3])
            )
        )
    );

    // Stable inputs must produce stable outputs.
    check_stable_inputs_stable_outputs: assert property (
        @(posedge clk)
        $stable({a, b, cin}) |-> $stable({sum, cout})
    );

    // Adding zero with no carry-in passes operand a through.
    check_b_zero_passthrough: assert property (
        @(posedge clk)
        (b == 4'b0000 && cin == 1'b0) |-> (sum == a && cout == 1'b0)
    );

    // Adding zero with no carry-in passes operand b through.
    check_a_zero_passthrough: assert property (
        @(posedge clk)
        (a == 4'b0000 && cin == 1'b0) |-> (sum == b && cout == 1'b0)
    );

endmodule