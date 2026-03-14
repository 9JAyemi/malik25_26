module population_count_4bit_sva (
    input logic clk,
    input logic [3:0] in,
    input logic [1:0] out
);
    // Out is 0 when input has zero 1s (0000).
    map_0ones: assert property (
        @(posedge clk) (in == 4'b0000) |-> (out == 2'b00)
    );

    // Out is 1 when input has exactly one 1.
    map_1one: assert property (
        @(posedge clk) (in inside {4'b0001, 4'b0010, 4'b0100, 4'b1000}) |-> (out == 2'b01)
    );

    // Out is 2 when input has exactly two 1s.
    map_2ones: assert property (
        @(posedge clk) (in inside {4'b0011, 4'b0101, 4'b0110, 4'b1001, 4'b1010, 4'b1100}) |-> (out == 2'b10)
    );

    // Out is 3 when input has three or four 1s (saturating at 3).
    map_3or4ones: assert property (
        @(posedge clk) (in inside {4'b0111, 4'b1011, 4'b1101, 4'b1110, 4'b1111}) |-> (out == 2'b11)
    );
endmodule