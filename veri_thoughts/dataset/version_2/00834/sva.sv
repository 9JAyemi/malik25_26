module two_bit_output_sva (
    input logic clk,
    input logic [3:0] b,
    input logic [1:0] so
);
    // Next cycle so=00 when b is 0,1,2.
    map_b_0_1_2_to_so_00: assert property (
        @(posedge clk) (b inside {4'd0,4'd1,4'd2}) |=> (so == 2'b00)
    );

    // Next cycle so=01 when b is 3 or 4.
    map_b_3_4_to_so_01: assert property (
        @(posedge clk) (b inside {4'd3,4'd4}) |=> (so == 2'b01)
    );

    // Next cycle so=10 when b is 5 or 6.
    map_b_5_6_to_so_10: assert property (
        @(posedge clk) (b inside {4'd5,4'd6}) |=> (so == 2'b10)
    );

    // Next cycle so=11 when b is 7.
    map_b_7_to_so_11: assert property (
        @(posedge clk) (b == 4'd7) |=> (so == 2'b11)
    );

    // Next cycle so=00 for default cases b=8..15.
    map_b_8_to_15_default_to_so_00: assert property (
        @(posedge clk) (b inside {[4'd8:4'd15]}) |=> (so == 2'b00)
    );

    // For b=3..7, next cycle so is never 00.
    not_00_for_b_3_to_7: assert property (
        @(posedge clk) (b inside {[4'd3:4'd7]}) |=> (so != 2'b00)
    );

    // Only b=3 or 4 produce next cycle so=01.
    only_3_4_give_01: assert property (
        @(posedge clk) (!(b inside {4'd3,4'd4})) |=> (so != 2'b01)
    );

    // Only b=5 or 6 produce next cycle so=10.
    only_5_6_give_10: assert property (
        @(posedge clk) (!(b inside {4'd5,4'd6})) |=> (so != 2'b10)
    );

    // Only b=7 produces next cycle so=11.
    only_7_gives_11: assert property (
        @(posedge clk) (b != 4'd7) |=> (so != 2'b11)
    );
endmodule