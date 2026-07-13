module simple_adder_sva(
    input logic clk,
    input logic rst,
    input logic [7:0] A,
    input logic [7:0] B,
    input logic [7:0] C
);

    // C matches the previous cycle's reset-or-add behavior.
    check_registered_behavior: assert property (
        @(posedge clk) disable iff ($initstate || rst)
        C == ($past(rst) ? 8'h00 : $past(A + B))
    );

    // A high reset drives C to zero on the following cycle.
    check_reset_clears_c: assert property (
        @(posedge clk)
        rst |=> (C == 8'h00)
    );

    // Without reset, C captures A+B on the following cycle.
    check_add_result_updates: assert property (
        @(posedge clk) disable iff (rst)
        !rst |=> (C == $past(A + B))
    );

    // When B is zero, C captures A on the following cycle.
    check_b_zero_passes_a: assert property (
        @(posedge clk) disable iff (rst)
        (B == 8'h00) |=> (C == $past(A))
    );

    // When A is zero, C captures B on the following cycle.
    check_a_zero_passes_b: assert property (
        @(posedge clk) disable iff (rst)
        (A == 8'h00) |=> (C == $past(B))
    );

    // 8-bit overflow wraps for 8'hFF plus 8'h01.
    check_overflow_wraps: assert property (
        @(posedge clk) disable iff (rst)
        (A == 8'hFF && B == 8'h01) |=> (C == 8'h00)
    );

endmodule