module sector_flash_map_sva #(
    parameter [2:0] SECTOR1_MAP = 3'b000,
    parameter [2:0] SECTOR2_MAP = 3'b001,
    parameter [2:0] SECTOR3_MAP = 3'b010,
    parameter [2:0] SECTOR4_MAP = 3'b011,
    parameter [2:0] SECTOR5_MAP = 3'b100
) (
    input logic CLK,
    input logic [2:0] sector,
    input logic [2:0] flash_sector
);
    ///// Functional mapping /////
    // flash_sector equals the combinational mapping function of sector.
    check_mapping_function_equivalence: assert property (
        @(posedge CLK)
        flash_sector == (
            (sector == 3'd1) ? SECTOR1_MAP :
            (sector == 3'd2) ? SECTOR2_MAP :
            (sector == 3'd3) ? SECTOR3_MAP :
            (sector == 3'd4) ? SECTOR4_MAP :
            (sector == 3'd5) ? SECTOR5_MAP :
            3'b000
        )
    );

    // Sector 1 maps to SECTOR1_MAP.
    check_map_sector1: assert property (
        @(posedge CLK) (sector == 3'd1) |-> (flash_sector == SECTOR1_MAP)
    );

    // Sector 2 maps to SECTOR2_MAP.
    check_map_sector2: assert property (
        @(posedge CLK) (sector == 3'd2) |-> (flash_sector == SECTOR2_MAP)
    );

    // Sector 3 maps to SECTOR3_MAP.
    check_map_sector3: assert property (
        @(posedge CLK) (sector == 3'd3) |-> (flash_sector == SECTOR3_MAP)
    );

    // Sector 4 maps to SECTOR4_MAP.
    check_map_sector4: assert property (
        @(posedge CLK) (sector == 3'd4) |-> (flash_sector == SECTOR4_MAP)
    );

    // Sector 5 maps to SECTOR5_MAP.
    check_map_sector5: assert property (
        @(posedge CLK) (sector == 3'd5) |-> (flash_sector == SECTOR5_MAP)
    );

    // Invalid sector 0 maps to 3'b000.
    check_invalid_sector_0: assert property (
        @(posedge CLK) (sector == 3'd0) |-> (flash_sector == 3'b000)
    );

    // Invalid sector 6 maps to 3'b000.
    check_invalid_sector_6: assert property (
        @(posedge CLK) (sector == 3'd6) |-> (flash_sector == 3'b000)
    );

    // Invalid sector 7 maps to 3'b000.
    check_invalid_sector_7: assert property (
        @(posedge CLK) (sector == 3'd7) |-> (flash_sector == 3'b000)
    );

    // flash_sector can only change when sector changes (pure combinational function).
    check_output_changes_only_with_input: assert property (
        @(posedge CLK) (sector == $past(sector)) |-> (flash_sector == $past(flash_sector))
    );

    // flash_sector is always one of the defined map values or 3'b000.
    check_output_membership: assert property (
        @(posedge CLK) flash_sector inside {SECTOR1_MAP, SECTOR2_MAP, SECTOR3_MAP, SECTOR4_MAP, SECTOR5_MAP, 3'b000}
    );
endmodule