```systemverilog
module sector_flash_map_sva (
    input logic [2:0] sector,
    output logic [2:0] flash_sector
);
    // Sequential logic assertion to check the mapping behavior
    map_behavior: assert property (
        @(posedge sector) disable iff (sector == 3'd0) (flash_sector == 
            (sector == 3'd1) ? 3'b000 :
            (sector == 3'd2) ? 3'b001 :
            (sector == 3'd3) ? 3'b010 :
            (sector == 3'd4) ? 3'b011 :
            (sector == 3'd5) ? 3'b100 :
            3'b000) // Set to 0 for invalid sector ID
    );
endmodule
```