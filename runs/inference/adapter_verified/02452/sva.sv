module top_module_sva (
    input logic        clk,
    input logic [15:0] in,
    input logic [7:0]  a,
    input logic [7:0]  b,
    input logic [7:0]  out
);

// No RTL reset; sample combinational behavior on clk.

    // out equals the low byte of a*b (8-bit wrap).
    check_out_matches_low_byte_product: assert property (
        @(posedge clk) out == (a * b)[7:0]
    );

// Upper byte of a*b is discarded when assigned to out.
    check_out_discards_upper_byte: assert property (
        @(posedge clk) out == (a * b)[7:0]
    );

// Zero on a forces out to zero.
    check_zero_a_forces_zero_out: assert property (
        @(posedge clk) (a == 8'h00) |-> (out == 8'h00)
    );

// Zero on b forces out to zero.
    check_zero_b_forces_zero_out: assert property (
        @(posedge clk) (b == 8'h00) |-> (out == 8'h00)
    );

// 8'hFF on a with b==1 returns 8'hFF.
    check_ff_times_one: assert property (
        @(posedge clk) (a == 8'hFF && b == 8'h01) |-> (out == 8'hFF)
    );

// 8'hFF on b with a==1 returns 8'hFF.
    check_ff_times_one_reverse: assert property (
        @(posedge clk) (b == 8'hFF && a == 8'h01) |-> (out == 8'hFF)
    );

// 8'h80 on a with b==2 returns 8'h00 (8-bit wrap).
    check_80_times_two: assert property (
        @(posedge clk) (a == 8'h80 && b == 8'h02) |-> (out == 8'h00)
    );

// 8'h80 on b with a==2 returns 8'h00 (8-bit wrap).
    check_80_times_two_reverse: assert property (
        @(posedge clk) (b == 8'h80 && a == 8'h02) |-> (out == 8'h00)
    );

// 8'hFF on a with b==2 returns 8'hFE (8-bit wrap).
    check_ff_times_two: assert property (
        @(posedge clk) (a == 8'hFF && b == 8'h02) |-> (out == 8'hFE)
    );

// 8'hFF on b with a==2 returns 8'hFE (8-bit wrap).
    check_ff_times_two_reverse: assert property (
        @(posedge clk) (b == 8'hFF && a == 8'h02) |-> (out == 8'hFE)
    );

endmodule
