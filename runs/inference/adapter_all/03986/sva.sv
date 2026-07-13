module simple_adder_sva (
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);
    // C is zero on the cycle after reset is asserted.
    reset_clears_C_next: assert property (
        @(posedge clk) rst |=> (C == 8'h00)
    );

    // When not in reset, C equals the sum of A and B from the previous cycle.
    add_result_matches_prev_inputs: assert property (
        @(posedge clk) disable iff (rst) C == $past(A + B)
    );

    // If A and B are stable over a cycle, C remains stable on the next cycle.
    stable_inputs_hold_output: assert property (
        @(posedge clk) disable iff (rst) ($stable(A) && $stable(B)) |=> $stable(C)
    );

    // If A and B are both zero, C is zero on the next cycle.
    zero_inputs_zero_output: assert property (
        @(posedge clk) disable iff (rst) (A == 8'h00 && B == 8'h00) |=> (C == 8'h00)
    );

    // If A is zero, C equals B on the next cycle.
    zero_A_passthrough_B: assert property (
        @(posedge clk) disable iff (rst) (A == 8'h00) |=> (C == $past(B))
    );

    // If B is zero, C equals A on the next cycle.
    zero_B_passthrough_A: assert property (
        @(posedge clk) disable iff (rst) (B == 8'h00) |=> (C == $past(A))
    );

    // If A is 8'hFF and B is 8'h01, C is zero on the next cycle (8-bit wrap).
    FF_plus_1_wraps_to_0: assert property (
        @(posedge clk) disable iff (rst) (A == 8'hFF && B == 8'h01) |=> (C == 8'h00)
    );

    // If A is 8'h01 and B is 8'hFF, C is zero on the next cycle (8-bit wrap).
    1_plus_FF_wraps_to_0: assert property (
        @(posedge clk) disable iff (rst) (A == 8'h01 && B == 8'hFF) |=> (C == 8'h00)
    );

    // If A is 8'hFF and B is 8'hFF, C is 8'hFE on the next cycle (8-bit wrap).
    FF_plus_FF_wraps_to_FE: assert property (
        @(posedge clk) disable iff (rst) (A == 8'hFF && B == 8'hFF) |=> (C == 8'hFE)
    );

    // If A is 8'h80 and B is 8'h80, C is 8'h00 on the next cycle (8-bit wrap).
    80h_plus_80h_wraps_to_0: assert property (
        @(posedge clk) disable iff (rst) (A == 8'h80 && B == 8'h80) |=> (C == 8'h00)
    );
endmodule