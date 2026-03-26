module calculator_sva (
    input logic clk,
    input logic [3:0] A,
    input logic [3:0] B,
    input logic [1:0] op,
    input logic [3:0] sum,
    input logic [3:0] diff,
    input logic [3:0] prod,
    input logic [3:0] quot
);

    // Addition mode updates sum and clears the other outputs.
    check_addition_mode: assert property (
        @(posedge clk)
        (op == 2'b00) |-> ((sum  == ((A + B) & 4'hF)) &&
                           (diff == 4'h0) &&
                           (prod == 4'h0) &&
                           (quot == 4'h0))
    );

    // Subtraction mode updates diff and clears the other outputs.
    check_subtraction_mode: assert property (
        @(posedge clk)
        (op == 2'b01) |-> ((sum  == 4'h0) &&
                           (diff == ((A - B) & 4'hF)) &&
                           (prod == 4'h0) &&
                           (quot == 4'h0))
    );

    // Multiplication mode updates prod and clears the other outputs.
    check_multiplication_mode: assert property (
        @(posedge clk)
        (op == 2'b10) |-> ((sum  == 4'h0) &&
                           (diff == 4'h0) &&
                           (prod == ((A * B) & 4'hF)) &&
                           (quot == 4'h0))
    );

    // Division by zero forces quot low and clears the other outputs.
    check_division_by_zero_mode: assert property (
        @(posedge clk)
        ((op == 2'b11) && (B == 4'h0)) |-> ((sum  == 4'h0) &&
                                            (diff == 4'h0) &&
                                            (prod == 4'h0) &&
                                            (quot == 4'h0))
    );

    // Division mode updates quot for nonzero divisor and clears the other outputs.
    check_division_mode: assert property (
        @(posedge clk)
        ((op == 2'b11) && (B != 4'h0)) |-> ((sum  == 4'h0) &&
                                            (diff == 4'h0) &&
                                            (prod == 4'h0) &&
                                            (quot == ((A / B) & 4'hF)))
    );

endmodule