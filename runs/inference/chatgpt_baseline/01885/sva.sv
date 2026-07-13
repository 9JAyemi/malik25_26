module rominfr_sva (
    input logic clk,
    input logic en,
    input logic [4:0] addr,
    input logic [3:0] data
);
    // Clock: clk posedge. No reset.
    // Sequential: data updates on en; holds when en==0.
    // Behavior: ROM mapping for addr 0..15; default assigns X.

    // Data holds its value when en is LOW.
    hold_when_en_low: assert property (
        @(posedge clk) !en |=> $stable(data)
    );

    // When en is HIGH and addr==0, next data is 0010.
    map_addr_0: assert property (
        @(posedge clk) en && (addr == 5'b00000) |=> (data == 4'b0010)
    );
    // When en is HIGH and addr==1, next data is 0010.
    map_addr_1: assert property (
        @(posedge clk) en && (addr == 5'b00001) |=> (data == 4'b0010)
    );
    // When en is HIGH and addr==2, next data is 1110.
    map_addr_2: assert property (
        @(posedge clk) en && (addr == 5'b00010) |=> (data == 4'b1110)
    );
    // When en is HIGH and addr==3, next data is 0010.
    map_addr_3: assert property (
        @(posedge clk) en && (addr == 5'b00011) |=> (data == 4'b0010)
    );
    // When en is HIGH and addr==4, next data is 0100.
    map_addr_4: assert property (
        @(posedge clk) en && (addr == 5'b00100) |=> (data == 4'b0100)
    );
    // When en is HIGH and addr==5, next data is 1010.
    map_addr_5: assert property (
        @(posedge clk) en && (addr == 5'b00101) |=> (data == 4'b1010)
    );
    // When en is HIGH and addr==6, next data is 1100.
    map_addr_6: assert property (
        @(posedge clk) en && (addr == 5'b00110) |=> (data == 4'b1100)
    );
    // When en is HIGH and addr==7, next data is 0000.
    map_addr_7: assert property (
        @(posedge clk) en && (addr == 5'b00111) |=> (data == 4'b0000)
    );
    // When en is HIGH and addr==8, next data is 1010.
    map_addr_8: assert property (
        @(posedge clk) en && (addr == 5'b01000) |=> (data == 4'b1010)
    );
    // When en is HIGH and addr==9, next data is 0010.
    map_addr_9: assert property (
        @(posedge clk) en && (addr == 5'b01001) |=> (data == 4'b0010)
    );
    // When en is HIGH and addr==10, next data is 1110.
    map_addr_10: assert property (
        @(posedge clk) en && (addr == 5'b01010) |=> (data == 4'b1110)
    );
    // When en is HIGH and addr==11, next data is 0010.
    map_addr_11: assert property (
        @(posedge clk) en && (addr == 5'b01011) |=> (data == 4'b0010)
    );
    // When en is HIGH and addr==12, next data is 0100.
    map_addr_12: assert property (
        @(posedge clk) en && (addr == 5'b01100) |=> (data == 4'b0100)
    );
    // When en is HIGH and addr==13, next data is 1010.
    map_addr_13: assert property (
        @(posedge clk) en && (addr == 5'b01101) |=> (data == 4'b1010)
    );
    // When en is HIGH and addr==14, next data is 1100.
    map_addr_14: assert property (
        @(posedge clk) en && (addr == 5'b01110) |=> (data == 4'b1100)
    );
    // When en is HIGH and addr==15, next data is 0000.
    map_addr_15: assert property (
        @(posedge clk) en && (addr == 5'b01111) |=> (data == 4'b0000)
    );

    // For en HIGH and addr in 0..15, next data is not X/Z.
    nonx_when_valid_addr: assert property (
        @(posedge clk) en && (addr[4] == 1'b0) |=> !$isunknown(data)
    );
endmodule