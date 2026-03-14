module next_state_logic_sva (
    input logic x,
    input logic [2:0] y,
    input logic Y2
);
    // For y==000, Y2 must equal x.
    check_y000_maps_to_x: assert property (
        @(posedge x) (y == 3'b000) |-> (Y2 == x)
    );

    // For y==001, Y2 must be 0.
    check_y001_maps_to_0: assert property (
        @(posedge x) (y == 3'b001) |-> (Y2 == 1'b0)
    );

    // For y==010, Y2 must equal x.
    check_y010_maps_to_x: assert property (
        @(posedge x) (y == 3'b010) |-> (Y2 == x)
    );

    // For y==011, Y2 must be 1.
    check_y011_maps_to_1: assert property (
        @(posedge x) (y == 3'b011) |-> (Y2 == 1'b1)
    );

    // For y==100, Y2 must be 1.
    check_y100_maps_to_1: assert property (
        @(posedge x) (y == 3'b100) |-> (Y2 == 1'b1)
    );

    // For y==101, Y2 must equal x.
    check_y101_maps_to_x: assert property (
        @(posedge x) (y == 3'b101) |-> (Y2 == x)
    );

    // For y==110, Y2 must be 0 (default case).
    check_y110_maps_to_0: assert property (
        @(posedge x) (y == 3'b110) |-> (Y2 == 1'b0)
    );

    // For y==111, Y2 must be 0 (default case).
    check_y111_maps_to_0: assert property (
        @(posedge x) (y == 3'b111) |-> (Y2 == 1'b0)
    );
endmodule