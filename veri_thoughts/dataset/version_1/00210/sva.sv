module draw_block_assertions(
    input logic clock,
    input logic [10:0] vcounter,
    input logic [11:0] hcounter,
    input logic [2:0] block,
    input logic [4:0] sel_row,
    input logic [4:0] sel_col,
    input logic [3:0] out
);

localparam [11:0] LEFT   = 12'd160;
localparam [11:0] RIGHT  = 12'd480;
localparam [11:0] TILE_W = 12'd32;
localparam [10:0] BOTTOM = 11'd480;
localparam [10:0] TILE_H = 11'd16;

// sel_col matches the 32-pixel horizontal tile index in the draw region.
check_sel_col_decode: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT))
    |-> (sel_col == ((hcounter - LEFT) / TILE_W))
);

// sel_row matches the 16-pixel vertical tile index in the draw region.
check_sel_row_decode: assert property (
    @(posedge clock)
    (vcounter < BOTTOM)
    |-> (sel_row == (vcounter / TILE_H))
);

// out is blank outside the active drawing window.
check_out_zero_outside_window: assert property (
    @(posedge clock)
    (!((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM)))
    |-> (out == 4'b0000)
);

// block 000 always produces blank output in range.
check_block_zero_blank: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b000))
    |-> (out == 4'b0000)
);

// Nonzero narrow blocks draw 8 on the top and bottom of the center strip.
check_narrow_center_border: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block != 3'b000) && (block[2] == 1'b0) &&
     (((hcounter - LEFT) % TILE_W) > 12'd8) &&
     (((hcounter - LEFT) % TILE_W) < 12'd23) &&
     (((vcounter % TILE_H) == 11'd0) || ((vcounter % TILE_H) == 11'd15)))
    |-> (out == 4'b1000)
);

// block 001 fills the center strip interior with 1100.
check_narrow_center_fill_block_001: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b001) &&
     (((hcounter - LEFT) % TILE_W) > 12'd8) &&
     (((hcounter - LEFT) % TILE_W) < 12'd23) &&
     ((vcounter % TILE_H) != 11'd0) && ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1100)
);

// block 010 fills the center strip interior with 1011.
check_narrow_center_fill_block_010: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b010) &&
     (((hcounter - LEFT) % TILE_W) > 12'd8) &&
     (((hcounter - LEFT) % TILE_W) < 12'd23) &&
     ((vcounter % TILE_H) != 11'd0) && ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1011)
);

// block 011 fills the center strip interior with 1101.
check_narrow_center_fill_block_011: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b011) &&
     (((hcounter - LEFT) % TILE_W) > 12'd8) &&
     (((hcounter - LEFT) % TILE_W) < 12'd23) &&
     ((vcounter % TILE_H) != 11'd0) && ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1101)
);

// Nonzero narrow blocks draw 8 on the two center-strip side columns.
check_narrow_side_columns_border: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block != 3'b000) && (block[2] == 1'b0) &&
     ((((hcounter - LEFT) % TILE_W) == 12'd8) ||
      (((hcounter - LEFT) % TILE_W) == 12'd23)))
    |-> (out == 4'b1000)
);

// Narrow blocks other than 011 are blank in the outer columns.
check_narrow_outer_blank_non_011: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block[2] == 1'b0) && (block[1:0] != 2'b11) &&
     ((((hcounter - LEFT) % TILE_W) < 12'd8) ||
      (((hcounter - LEFT) % TILE_W) > 12'd23)))
    |-> (out == 4'b0000)
);

// block 011 draws 8 on the tile border in the outer columns.
check_narrow_outer_block_011_border: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b011) &&
     ((((hcounter - LEFT) % TILE_W) < 12'd8) ||
      (((hcounter - LEFT) % TILE_W) > 12'd23)) &&
     ((((hcounter - LEFT) % TILE_W) == 12'd0) ||
      (((hcounter - LEFT) % TILE_W) == 12'd31) ||
      ((vcounter % TILE_H) == 11'd0) ||
      ((vcounter % TILE_H) == 11'd15)))
    |-> (out == 4'b1000)
);

// block 011 fills the outer-column tile interior with 1110.
check_narrow_outer_block_011_fill: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b011) &&
     ((((hcounter - LEFT) % TILE_W) < 12'd8) ||
      (((hcounter - LEFT) % TILE_W) > 12'd23)) &&
     (((hcounter - LEFT) % TILE_W) != 12'd0) &&
     (((hcounter - LEFT) % TILE_W) != 12'd31) &&
     ((vcounter % TILE_H) != 11'd0) &&
     ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1110)
);

// Wide blocks draw 8 on the tile border.
check_wide_border: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block[2] == 1'b1) &&
     ((((hcounter - LEFT) % TILE_W) == 12'd0) ||
      (((hcounter - LEFT) % TILE_W) == 12'd31) ||
      ((vcounter % TILE_H) == 11'd0) ||
      ((vcounter % TILE_H) == 11'd15)))
    |-> (out == 4'b1000)
);

// block 100 fills the wide tile interior with 1001.
check_wide_fill_block_100: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b100) &&
     (((hcounter - LEFT) % TILE_W) != 12'd0) &&
     (((hcounter - LEFT) % TILE_W) != 12'd31) &&
     ((vcounter % TILE_H) != 11'd0) &&
     ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1001)
);

// block 101 fills the wide tile interior with 1010.
check_wide_fill_block_101: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b101) &&
     (((hcounter - LEFT) % TILE_W) != 12'd0) &&
     (((hcounter - LEFT) % TILE_W) != 12'd31) &&
     ((vcounter % TILE_H) != 11'd0) &&
     ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1010)
);

// block 110 fills the wide tile interior with 1110.
check_wide_fill_block_110: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b110) &&
     (((hcounter - LEFT) % TILE_W) != 12'd0) &&
     (((hcounter - LEFT) % TILE_W) != 12'd31) &&
     ((vcounter % TILE_H) != 11'd0) &&
     ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1110)
);

// block 111 fills the wide tile interior with 1111.
check_wide_fill_block_111: assert property (
    @(posedge clock)
    ((hcounter >= LEFT) && (hcounter < RIGHT) && (vcounter < BOTTOM) &&
     (block == 3'b111) &&
     (((hcounter - LEFT) % TILE_W) != 12'd0) &&
     (((hcounter - LEFT) % TILE_W) != 12'd31) &&
     ((vcounter % TILE_H) != 11'd0) &&
     ((vcounter % TILE_H) != 11'd15))
    |-> (out == 4'b1111)
);

endmodule