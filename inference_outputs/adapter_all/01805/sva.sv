module multiplier_sva (
    input logic [7:0] num1,
    input logic [7:0] num2,
    input logic [15:0] product
);
    // Product equals the 8x8 unsigned multiplication of inputs.
    check_product_matches_mul: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        product == (num1 * num2)
    );

    // If either operand is zero, the product is zero.
    check_zero_operand_zero_product: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h00) || (num2 == 8'h00)) |-> (product == 16'h0000)
    );

    // If either operand is one, the product equals the other operand.
    check_one_operand_identity: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h01) || (num2 == 8'h01)) |-> (product == (num1 | num2))
    );

    // If either operand is eight, the product is the other operand shifted left by 3.
    check_eight_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h08) || (num2 == 8'h08)) |-> (product == (num1 << 3) | (num2 << 3))
    );

    // If either operand is fifteen, the product is the other operand shifted left by 4.
    check_fifteen_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h0F) || (num2 == 8'h0F)) |-> (product == (num1 << 4) | (num2 << 4))
    );

    // If either operand is sixteen, the product is the other operand shifted left by 4.
    check_sixteen_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h10) || (num2 == 8'h10)) |-> (product == (num1 << 4) | (num2 << 4))
    );

    // If either operand is thirty-one, the product is the other operand shifted left by 5.
    check_thirtyone_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h1F) || (num2 == 8'h1F)) |-> (product == (num1 << 5) | (num2 << 5))
    );

    // If either operand is thirty-two, the product is the other operand shifted left by 5.
    check_thirtytwo_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h20) || (num2 == 8'h20)) |-> (product == (num1 << 5) | (num2 << 5))
    );

    // If either operand is sixty-three, the product is the other operand shifted left by 6.
    check_sixtythree_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h3F) || (num2 == 8'h3F)) |-> (product == (num1 << 6) | (num2 << 6))
    );

    // If either operand is sixty-four, the product is the other operand shifted left by 6.
    check_sixtyfour_operand_shift: assert property (
        @(posedge num1[0] or posedge num1[1] or posedge num1[2] or posedge num1[3] or
          posedge num1[4] or posedge num1[5] or posedge num1[6] or posedge num1[7] or
          posedge num2[0] or posedge num2[1] or posedge num2[2] or posedge num2[3] or
          posedge num2[4] or posedge num2[5] or posedge num2[6] or posedge num2[7])
        ((num1 == 8'h40) || (num2 == 