module add_sub_sva (
    input logic clk,
    input logic reset,
    input logic operation,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [3:0] result
);

// Reset clears result on the next clock.
    check_reset_clears_result: assert property (
        @(posedge clk) !reset |=> (result == 4'b0000)
    );

// In add mode, result captures A + B on the next clock.
    check_add_mode_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b0) |=> (result == ($past(A) + $past(B)))
    );

// In subtract mode, result captures A - B on the next clock.
    check_sub_mode_result: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b1) |=> (result == ($past(A) - $past(B)))
    );

// In add mode with B == 0, result holds A on the next clock.
    check_add_identity: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b0 && B == 4'b0000) |=> (result == $past(A))
    );

// In subtract mode with B == 0, result holds A on the next clock.
    check_sub_identity: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b1 && B == 4'b0000) |=> (result == $past(A))
    );

// In add mode with A == 0, result holds B on the next clock.
    check_add_zero_a: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b0 && A == 4'b0000) |=> (result == $past(B))
    );

// In subtract mode with A == 0, result is -B (2's complement) on the next clock.
    check_sub_zero_a: assert property (
        @(posedge clk) disable iff (!reset)
        (operation == 1'b1 && A == 4'b0000) |=> (result == ~$past(B) + 4'b0001)
    );

endmodule
