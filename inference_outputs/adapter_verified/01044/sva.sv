module signal_processor_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [3:0] out
);

// For inputs 0 through 3, out equals in * 2 (4-bit wrap).
    check_lt4_double: assert property (
        @(posedge clk) (in < 4'd4) |-> (out == (in * 4'd2))
    );

// For inputs 4 through 7, out equals in * in (4-bit wrap).
    check_4to7_square: assert property (
        @(posedge clk) (in <= 4'd7) |-> (out == (in * in))
    );

// For inputs 8 through 15, out equals in / 2 (integer division).
    check_gt7_div2: assert property (
        @(posedge clk) (in > 4'd7) |-> (out == (in / 4'd2))
    );

// For inputs 0 through 3, out is even (4-bit wrap).
    check_lt4_even: assert property (
        @(posedge clk) (in < 4'd4) |-> (out[0] == 1'b0)
    );

// For inputs 4 through 7, out equals in * in (4-bit wrap).
    check_4to7_square: assert property (
        @(posedge clk) (in <= 4'd7) |-> (out == (in * in))
    );

// For inputs 8 through 15, out equals in / 2 (integer division).
    check_gt7_div2: assert property (
        @(posedge clk) (in > 4'd7) |-> (out == (in / 4'd2))
    );

// For inputs 0 through 3, out is even (4-bit wrap).
    check_lt4_even: assert property (
        @(posedge clk) (in < 4'd4) |-> (out[0] == 1'b0)
    );

// For inputs 4 through 7, out equals in * in (4-bit wrap).
    check_4to7_square: assert property (
        @(posedge clk) (in <= 4'd7) |-> (out == (in * in))
    );

// For inputs 8 through 15, out equals in / 2 (integer division).
    check_gt7_div2: assert property (
        @(posedge clk) (in > 4'd7) |-> (out == (in / 4'd2))
    );

endmodule
