module HallwayRight_sva (
    input logic        clk_vga,
    input logic [9:0]  CurrentX,
    input logic [8:0]  CurrentY,
    input logic [7:0]  wall,
    input logic [7:0]  mapData
);

    // Top strip uses the wall color.
    check_top_strip_wall: assert property (
        @(posedge clk_vga)
        (CurrentY < 9'd40) |=> (mapData == $past(wall))
    );

    // Right side uses the wall color.
    check_right_side_wall: assert property (
        @(posedge clk_vga)
        (CurrentX >= 10'd600) |=> (mapData == $past(wall))
    );

    // Bottom-left region uses the wall color.
    check_bottom_left_wall: assert property (
        @(posedge clk_vga)
        (CurrentY >= 9'd440 && CurrentX < 10'd260) |=> (mapData == $past(wall))
    );

    // Bottom-right region uses the wall color.
    check_bottom_right_wall: assert property (
        @(posedge clk_vga)
        (CurrentY >= 9'd440 && CurrentX >= 10'd380) |=> (mapData == $past(wall))
    );

    // Upper interior region uses the default color.
    check_upper_interior_default: assert property (
        @(posedge clk_vga)
        (CurrentY >= 9'd40 && CurrentY < 9'd440 && CurrentX < 10'd600) |=> (mapData == 8'b10110110)
    );

    // Lower center opening uses the default color.
    check_lower_center_default: assert property (
        @(posedge clk_vga)
        (CurrentY >= 9'd440 && CurrentX >= 10'd260 && CurrentX < 10'd380) |=> (mapData == 8'b10110110)
    );

endmodule