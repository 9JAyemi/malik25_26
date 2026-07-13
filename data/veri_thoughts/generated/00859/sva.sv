module BlackKeyRoom_sva (
    input logic clk_vga,
    input logic [9:0] CurrentX,
    input logic [8:0] CurrentY,
    input logic [7:0] wall,
    input logic [7:0] mapData
);
    ///// Design uses clk_vga, no reset present /////
    // Next cycle mapData follows the priority if-else chain driven by prior-cycle inputs.
    check_map_priority_function: assert property (
        @(posedge clk_vga)
            1'b1 |=> mapData == (
                ( (( $past(CurrentY) < 9'd40) && ( $past(CurrentX) < 10'd260)) ||
                  (( $past(CurrentY) < 9'd40) && ~( $past(CurrentX) < 10'd380)) ) ? $past(wall) :
                (  $past(CurrentX) < 10'd40 )                                 ? $past(wall) :
                ( ~($past(CurrentX) < 10'd600) )                               ? $past(wall) :
                ( ~($past(CurrentY) < 9'd440) )                                ? $past(wall) :
                                                                                 8'b10110110
            )
    );

    // For Y<40 and X<260, next cycle mapData equals prior wall.
    check_wall_region_top_left: assert property (
        @(posedge clk_vga)
            ((CurrentY < 9'd40) && (CurrentX < 10'd260)) |=> (mapData == $past(wall))
    );

    // For Y<40 and not(X<380), next cycle mapData equals prior wall.
    check_wall_region_top_right: assert property (
        @(posedge clk_vga)
            ((CurrentY < 9'd40) && ~(CurrentX < 10'd380)) |=> (mapData == $past(wall))
    );

    // For X<40, next cycle mapData equals prior wall.
    check_wall_region_left_edge: assert property (
        @(posedge clk_vga)
            (CurrentX < 10'd40) |=> (mapData == $past(wall))
    );

    // For not(X<600) i.e., X>=600, next cycle mapData equals prior wall.
    check_wall_region_right_edge: assert property (
        @(posedge clk_vga)
            (~(CurrentX < 10'd600)) |=> (mapData == $past(wall))
    );

    // For not(Y<440) i.e., Y>=440, next cycle mapData equals prior wall.
    check_wall_region_bottom_edge: assert property (
        @(posedge clk_vga)
            (~(CurrentY < 9'd440)) |=> (mapData == $past(wall))
    );

    // For Y<40 and 260<=X<380, next cycle mapData equals the constant 8'b10110110.
    check_constant_region_top_gap: assert property (
        @(posedge clk_vga)
            ((CurrentY < 9'd40) && !(CurrentX < 10'd260) && (CurrentX < 10'd380)) |=> (mapData == 8'b10110110)
    );

    // When no wall conditions hold, next cycle mapData equals the constant 8'b10110110.
    check_constant_when_no_wall_conds: assert property (
        @(posedge clk_vga)
            ( !(((CurrentY < 9'd40) && (CurrentX < 10'd260)) || ((CurrentY < 9'd40) && ~(CurrentX < 10'd380)))) &&
              !(CurrentX < 10'd40) &&
              !(~(CurrentX < 10'd600)) &&
              !(~(CurrentY < 9'd440))
            |=> (mapData == 8'b10110110)
    );

    // Next cycle mapData is always either prior wall or the constant.
    check_only_wall_or_const: assert property (
        @(posedge clk_vga)
            1'b1 |=> ((mapData == $past(wall)) || (mapData == 8'b10110110))
    );

    // If next cycle mapData equals the constant, then no wall conditions held in the prior cycle.
    check_const_implies_no_wall_conds: assert property (
        @(posedge clk_vga)
            (mapData == 8'b10110110) |-> (
                !((($past(CurrentY) < 9'd40) && ($past(CurrentX) < 10'd260)) || (($past(CurrentY) < 9'd40) && ~($past(CurrentX) < 10'd380)))) &&
                !($past(CurrentX) < 10'd40) &&
                !(~($past(CurrentX) < 10'd600)) &&
                !(~($past(CurrentY) < 9'd440))
            )
    );

    // If next cycle mapData equals prior wall, then at least one wall condition held in the prior cycle.
    check_wall_implies_some_condition: assert property (
        @(posedge clk_vga)
            (mapData == $past(wall)) |-> (
                (( $past(CurrentY) < 9'd40) && ( $past(CurrentX) < 10'd260)) ||
                (( $past(CurrentY) < 9'd40) && ~( $past(CurrentX) < 10'd380)) ||
                (  $past(CurrentX) < 10'd40) ||
                ( ~($past(CurrentX) < 10'd600)) ||
                ( ~($past(CurrentY) < 9'd440))
            )
    );

endmodule