module top_module_sva (
    input logic clk,
    input logic [15:0] A,
    input logic [15:0] B,
    input logic [3:0] SEL,
    input logic [15:0] result
);
    // Result matches the top-level combinational spec
    check_overall_functionality: assert property (
        @(posedge clk) result == (SEL[1] ? (SEL[0] ? (A >> B) : (A << B))
                                        : (SEL[0] ? (A - B) : (A + B)))
    );

    // When select is add/sub and mode=add, result equals A+B
    check_add_mode_add: assert property (
        @(posedge clk) (SEL[1] == 1'b0 && SEL[0] == 1'b0) |-> (result == (A + B))
    );

    // When select is add/sub and mode=sub, result equals A-B
    check_add_mode_sub: assert property (
        @(posedge clk) (SEL[1] == 1'b0 && SEL[0] == 1'b1) |-> (result == (A - B))
    );

    // When select is shift and dir=left, result equals A<<B
    check_shift_mode_left: assert property (
        @(posedge clk) (SEL[1] == 1'b1 && SEL[0] == 1'b0) |-> (result == (A << B))
    );

    // When select is shift and dir=right, result equals A>>B
    check_shift_mode_right: assert property (
        @(posedge clk) (SEL[1] == 1'b1 && SEL[0] == 1'b1) |-> (result == (A >> B))
    );

    // In shift path, zero shift amount returns A
    check_shift_zero_amount: assert property (
        @(posedge clk) (SEL[1] == 1'b1 && (B == 16'd0)) |-> (result == A)
    );

    // In add/sub path, B==0 returns A
    check_addsub_zero_B: assert property (
        @(posedge clk) (SEL[1] == 1'b0 && (B == 16'd0)) |-> (result == A)
    );

    // In subtract mode with equal operands, result is zero
    check_sub_equal_operands_zero: assert property (
        @(posedge clk) (SEL[1] == 1'b0 && SEL[0] == 1'b1 && (A == B)) |-> (result == 16'h0000)
    );

    // Right shift by amount >= width yields zero
    check_right_shift_ge_width_zero: assert property (
        @(posedge clk) (SEL[1] == 1'b1 && SEL[0] == 1'b1 && (B >= 16'd16)) |-> (result == 16'h0000)
    );

    // Left shift by amount >= width yields zero
    check_left_shift_ge_width_zero: assert property (
        @(posedge clk) (SEL[1] == 1'b1 && SEL[0] == 1'b0 && (B >= 16'd16)) |-> (result == 16'h0000)
    );
endmodule