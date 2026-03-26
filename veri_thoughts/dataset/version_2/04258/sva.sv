module alu_16_sva (
    input logic        clk,
    input logic [15:0] a,
    input logic [15:0] b,
    input logic [7:0]  ctrl,
    input logic [15:0] out,
    input logic        n,
    input logic        z,
    input logic        c,
    input logic        v
);

    // AND select drives the bitwise AND result.
    check_and_select: assert property (
        @(posedge clk) (ctrl == 8'h00) |-> (out == (a & b))
    );

    // OR select drives the bitwise OR result.
    check_or_select: assert property (
        @(posedge clk) (ctrl == 8'h01) |-> (out == (a | b))
    );

    // ADD select drives the sum result.
    check_add_select: assert property (
        @(posedge clk) (ctrl == 8'h02) |-> (out == (a + b))
    );

    // SUB select drives the difference result.
    check_sub_select: assert property (
        @(posedge clk) (ctrl == 8'h03) |-> (out == (a - b))
    );

    // SLT select drives 1 when a is less than b, else 0.
    check_slt_select: assert property (
        @(posedge clk) (ctrl == 8'h04) |-> (out == ((a < b) ? 16'h0001 : 16'h0000))
    );

    // SLL select shifts a left by b[3:0].
    check_sll_select: assert property (
        @(posedge clk) (ctrl == 8'h05) |-> (out == (a << b[3:0]))
    );

    // SRL select shifts a right logically by b[3:0].
    check_srl_select: assert property (
        @(posedge clk) (ctrl == 8'h06) |-> (out == (a >> b[3:0]))
    );

    // SRA select shifts a right arithmetically by b[3:0].
    check_sra_select: assert property (
        @(posedge clk) (ctrl == 8'h07) |-> (out == ($signed(a) >>> b[3:0]))
    );

    // Unrecognized control values drive zero on out.
    check_default_zero: assert property (
        @(posedge clk)
        ((ctrl != 8'h00) && (ctrl != 8'h01) && (ctrl != 8'h02) && (ctrl != 8'h03) &&
         (ctrl != 8'h04) && (ctrl != 8'h05) && (ctrl != 8'h06) && (ctrl != 8'h07))
        |-> (out == 16'h0000)
    );

    // n reflects the sign bit of out.
    check_negative_flag: assert property (
        @(posedge clk) (n == out[15])
    );

    // z is asserted only when out is zero.
    check_zero_flag: assert property (
        @(posedge clk) (z == (out == 16'h0000))
    );

    // c matches the sign bit of out in this RTL.
    check_carry_flag: assert property (
        @(posedge clk) (c == out[15])
    );

    // v follows the implemented sign-based overflow expression.
    check_overflow_flag: assert property (
        @(posedge clk)
        (v == ((((a[15] == 1'b0) && (b[15] == 1'b0) && (out[15] == 1'b1)) ||
                ((a[15] == 1'b1) && (b[15] == 1'b1) && (out[15] == 1'b0))) ? 1'b1 : 1'b0))
    );

endmodule