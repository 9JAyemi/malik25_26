module RippleAdder2_sva (
    input logic clk,
    input logic [3:0] a,
    input logic [3:0] b,
    input logic ci,
    input logic co,
    input logic [3:0] s
);

// s[0] is the XOR of the LSB inputs and carry-in.
    check_sum_bit0: assert property (
        @(posedge clk) s[0] == (a[0] ^ b[0] ^ ci)
    );

// s[1] uses the carry generated from bit 0.
    check_sum_bit1: assert property (
        @(posedge clk) s[1] == (
            a[1] ^ b[1] ^
            ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))
        )
    );

// s[2] uses the carry generated from bit 1.
    check_sum_bit2: assert property (
        @(posedge clk) s[2] == (
            a[2] ^ b[2] ^
            (
                (a[1] & b[1]) |
                (
                    (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                    (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                )
            )
        )
    );

// s[3] uses the carry generated from bit 2.
    check_sum_bit3: assert property (
        @(posedge clk) s[3] == (
            a[3] ^ b[3] ^
            (
                (a[2] & b[2]) |
                (
                    (a[2] & (
                        (a[1] & b[1]) |
                        (
                            (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                            (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                        )
                    )) |
                    (b[2] & (
                        (a[1] & b[1]) |
                        (
                            (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                            (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                        )
                    ))
                )
            )
        )
    );

// co is the carry generated from bit 3.
    check_carry_out: assert property (
        @(posedge clk) co == (
            (a[3] & b[3]) |
            (
                (a[3] & (
                    (a[2] & b[2]) |
                    (
                        (a[2] & (
                            (a[1] & b[1]) |
                            (
                                (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                                (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                            )
                        )) |
                        (b[2] & (
                            (a[1] & b[1]) |
                            (
                                (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                                (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                            )
                        ))
                    )
                )) |
                (b[3] & (
                    (a[2] & b[2]) |
                    (
                        (a[2] & (
                            (a[1] & b[1]) |
                            (
                                (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                                (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                            )
                        )) |
                        (b[2] & (
                            (a[1] & b[1]) |
                            (
                                (a[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci)))) |
                                (b[1] & ((a[0] & b[0]) | ((a[0] & ci) | (b[0] & ci))))
                            )
                        ))
                    )
                ))
            )
        )
    );

// All-zero inputs produce all-zero outputs.
    check_zero_case: assert property (
        @(posedge clk) (a == 4'b0000 && b == 4'b0000 && ci == 1'b0) |-> (s == 4'b0000 && co == 1'b0)
    );

// Adding zero with carry-in produces the input a.
    check_add_zero_to_a: assert property (
        @(posedge clk) (b == 4'b0000 && ci == 1'b1) |-> (s == a && co == 1'b0)
    );

// Adding zero with carry-in produces the input b.
    check_add_zero_to_b: assert property (
        @(posedge clk) (a == 4'b0000 && ci == 1'b1) |-> (s == b && co == 1'b0)
    );

// Adding equal operands with carry-in produces a carry-out.
    check_equal_operands_with_ci: assert property (
        @(posedge clk) (a == b && ci == 1'b1) |-> (s == 4'b0000 && co == 1'b1)
    );

// Adding equal operands without carry-in produces zero.
    check_equal_operands_without_ci: assert property (
        @(posedge clk) (a == b && ci == 1'b0) |-> (s == 4'b0000 && co == 1'b0)
    );

endmodule
