module sector_flash_map (
    input [2:0] sector,
    output [2:0] flash_sector
);

    parameter SECTOR1_MAP = 3'b000;
    parameter SECTOR2_MAP = 3'b001;
    parameter SECTOR3_MAP = 3'b010;
    parameter SECTOR4_MAP = 3'b011;
    parameter SECTOR5_MAP = 3'b100;

    assign flash_sector = 
        (sector == 3'd1) ? SECTOR1_MAP :
        (sector == 3'd2) ? SECTOR2_MAP :
        (sector == 3'd3) ? SECTOR3_MAP :
        (sector == 3'd4) ? SECTOR4_MAP :
        (sector == 3'd5) ? SECTOR5_MAP :
        3'b000; // Set to 0 for invalid sector ID

endmodule