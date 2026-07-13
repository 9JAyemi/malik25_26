module rectangle_area_sva (
    input logic       clk,
    input logic [3:0] length,
    input logic [3:0] width,
    input logic [7:0] area
);

    // Area must always equal length multiplied by width.
    check_area_matches_product: assert property (
        @(posedge clk) area == (length * width)
    );

    // Zero length must produce zero area.
    check_zero_length_gives_zero_area: assert property (
        @(posedge clk) (length == 4'd0) |-> (area == 8'd0)
    );

    // Zero width must produce zero area.
    check_zero_width_gives_zero_area: assert property (
        @(posedge clk) (width == 4'd0) |-> (area == 8'd0)
    );

    // Unit length must pass width through to area.
    check_unit_length_passthrough: assert property (
        @(posedge clk) (length == 4'd1) |-> (area == {4'b0, width})
    );

    // Unit width must pass length through to area.
    check_unit_width_passthrough: assert property (
        @(posedge clk) (width == 4'd1) |-> (area == {4'b0, length})
    );

    // Identical sampled inputs must reproduce the same sampled area.
    check_same_inputs_same_area: assert property (
        @(posedge clk) !$initstate && (length == $past(length)) && (width == $past(width)) |-> (area == $past(area))
    );

    // Maximum 4-bit inputs must produce 225.
    check_max_inputs_give_max_area: assert property (
        @(posedge clk) (length == 4'hF) && (width == 4'hF) |-> (area == 8'd225)
    );

endmodule