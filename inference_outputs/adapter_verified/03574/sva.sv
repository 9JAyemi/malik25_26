module square_module_sva (
    input logic clk,
    input logic [3:0] num,
    input logic [7:0] square
);

// Square must equal num * num.
    check_square_matches_multiplication: assert property (
        @(posedge clk) square == (num * num)
    );

// Zero input must produce zero output.
    check_zero_input: assert property (
        @(posedge clk) (num == 4'd0) |-> (square == 8'd0)
    );

// One input must produce one output.
    check_one_input: assert property (
        @(posedge clk) (num == 4'd1) |-> (square == 8'd1)
    );

// Four input must produce sixteen output.
    check_four_input: assert property (
        @(posedge clk) (num == 4'd4) |-> (square == 8'd16)
    );

// Eight input must produce sixty-four output.
    check_eight_input: assert property (
        @(posedge clk) (num == 4'd8) |-> (square == 8'd64)
    );

// Nine input must produce eighty-one output.
    check_nine_input: assert property (
        @(posedge clk) (num == 4'd9) |-> (square == 8'd81)
    );

// Maximum input must produce 15*15 = 225 output.
    check_max_input: assert property (
        @(posedge clk) (num == 4'hF) |-> (square == 8'd225)
    );

endmodule
