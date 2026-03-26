module rectangle_area_sva (
    input logic        clk,
    input logic [7:0]  length,
    input logic [7:0]  width,
    input logic [15:0] area
);

    // Area must always equal the product of length and width.
    check_area_matches_product: assert property (
        @(posedge clk) area == (length * width)
    );

    // Zero length must produce zero area.
    check_zero_length_gives_zero_area: assert property (
        @(posedge clk) (length == 8'h00) |-> (area == 16'h0000)
    );

    // Zero width must produce zero area.
    check_zero_width_gives_zero_area: assert property (
        @(posedge clk) (width == 8'h00) |-> (area == 16'h0000)
    );

    // Unit length must pass width through to area.
    check_unit_length_passthrough: assert property (
        @(posedge clk) (length == 8'h01) |-> (area == {8'h00, width})
    );

    // Unit width must pass length through to area.
    check_unit_width_passthrough: assert property (
        @(posedge clk) (width == 8'h01) |-> (area == {8'h00, length})
    );

    // Stable inputs must keep area stable across sampled cycles.
    check_stable_inputs_keep_area_stable: assert property (
        @(posedge clk) ($stable(length) && $stable(width)) |-> $stable(area)
    );

endmodule