module mult_16x16_sva (
    input logic CLK,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [31:0] Z
);
    // No clock/reset in DUT; pure combinational; assertions sampled on CLK.

    // Z must equal the unsigned product of A and B every cycle.
    check_mult16_product: assert property (
        @(posedge CLK) Z === (A * B)
    );

    // If either input is zero, the product is zero in the same cycle.
    check_mult16_zero_input: assert property (
        @(posedge CLK) ((A == '0) || (B == '0)) |-> (Z == '0)
    );

    // Multiplication by 1 (left operand) yields the other operand.
    check_mult16_identity_left: assert property (
        @(posedge CLK) (A == 16'd1) |-> (Z == B)
    );

    // Multiplication by 1 (right operand) yields the other operand.
    check_mult16_identity_right: assert property (
        @(posedge CLK) (B == 16'd1) |-> (Z == A)
    );
endmodule

module mult_20x18_sva (
    input logic CLK,
    input logic [19:0] A,
    input logic [17:0] B,
    input logic [37:0] Z
);
    // No clock/reset in DUT; pure combinational; assertions sampled on CLK.

    // Z must equal the unsigned product of A and B every cycle.
    check_mult20x18_product: assert property (
        @(posedge CLK) Z === (A * B)
    );

    // If either input is zero, the product is zero in the same cycle.
    check_mult20x18_zero_input: assert property (
        @(posedge CLK) ((A == '0) || (B == '0)) |-> (Z == '0)
    );

    // Multiplication by 1 (left operand) yields the other operand.
    check_mult20x18_identity_left: assert property (
        @(posedge CLK) (A == 20'd1) |-> (Z == B)
    );

    // Multiplication by 1 (right operand) yields the other operand.
    check_mult20x18_identity_right: assert property (
        @(posedge CLK) (B == 18'd1) |-> (Z == A)
    );
endmodule

module mult_8x8_sva (
    input logic CLK,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [15:0] Z
);
    // No clock/reset in DUT; pure combinational; assertions sampled on CLK.

    // Z must equal the unsigned product of A and B every cycle.
    check_mult8_product: assert property (
        @(posedge CLK) Z === (A * B)
    );

    // If either input is zero, the product is zero in the same cycle.
    check_mult8_zero_input: assert property (
        @(posedge CLK) ((A == '0) || (B == '0)) |-> (Z == '0)
    );

    // Multiplication by 1 (left operand) yields the other operand.
    check_mult8_identity_left: assert property (
        @(posedge CLK) (A == 8'd1) |-> (Z == B)
    );

    // Multiplication by 1 (right operand) yields the other operand.
    check_mult8_identity_right: assert property (
        @(posedge CLK) (B == 8'd1) |-> (Z == A)
    );
endmodule

module mult_10x9_sva (
    input logic CLK,
    input logic [9:0] A,
    input logic [8:0] B,
    input logic [18:0] Z
);
    // No clock/reset in DUT; pure combinational; assertions sampled on CLK.

    // Z must equal the unsigned product of A and B every cycle.
    check_mult10x9_product: assert property (
        @(posedge CLK) Z === (A * B)
    );

    // If either input is zero, the product is zero in the same cycle.
    check_mult10x9_zero_input: assert property (
        @(posedge CLK) ((A == '0) || (B == '0)) |-> (Z == '0)
    );

    // Multiplication by 1 (left operand) yields the other operand.
    check_mult10x9_identity_left: assert property (
        @(posedge CLK) (A == 10'd1) |-> (Z == B)
    );

    // Multiplication by 1 (right operand) yields the other operand.
    check_mult10x9_identity_right: assert property (
        @(posedge CLK) (B == 9'd1) |-> (Z == A)
    );
endmodule