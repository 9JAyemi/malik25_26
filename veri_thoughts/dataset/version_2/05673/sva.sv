module alu_sva (
    input logic        clk,
    input logic [31:0] a,
    input logic [31:0] b,
    input logic [4:0]  aluc,
    input logic [31:0] result
);

    // Opcode 0 returns a + b.
    check_add_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd0) |-> (result == (a + b))
    );

    // Opcode 1 returns a - b.
    check_sub_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd1) |-> (result == (a - b))
    );

    // Opcode 2 returns a & b.
    check_and_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd2) |-> (result == (a & b))
    );

    // Opcode 3 returns a | b.
    check_or_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd3) |-> (result == (a | b))
    );

    // Opcode 6 returns b shifted left by a.
    check_shift_left_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd6) |-> (result == (b << a))
    );

    // Opcode 10 returns b shifted right by a.
    check_shift_right_logical_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd10) |-> (result == (b >> a))
    );

    // Opcode 8 returns the RTL's implemented shift expression.
    check_case8_result: assert property (
        @(posedge clk) disable iff (1'b0)
        (aluc == 5'd8) |-> (result == ((b >> a) | ({32{b[31]}} << (32'd32))))
    );

    // Unlisted opcodes drive zero.
    check_default_zero_result: assert property (
        @(posedge clk) disable iff (1'b0)
        ((aluc != 5'd0) &&
         (aluc != 5'd1) &&
         (aluc != 5'd2) &&
         (aluc != 5'd3) &&
         (aluc != 5'd6) &&
         (aluc != 5'd8) &&
         (aluc != 5'd10)) |-> (result == 32'd0)
    );

endmodule