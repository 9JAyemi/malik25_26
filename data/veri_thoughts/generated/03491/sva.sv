module address_sva (
    input logic CLK,
    input logic [15:0] featurebits,
    input logic [2:0] MAPPER,
    input logic [23:0] SNES_ADDR,
    input logic [7:0] SNES_PA,
    input logic SNES_ROMSEL,
    input logic [23:0] ROM_ADDR,
    input logic ROM_HIT,
    input logic IS_SAVERAM,
    input logic IS_ROM,
    input logic IS_WRITABLE,
    input logic [23:0] SAVERAM_MASK,
    input logic [23:0] ROM_MASK,
    input logic msu_enable,
    input logic r213f_enable,
    input logic r2100_hit,
    input logic snescmd_enable,
    input logic nmicmd_enable,
    input logic return_vector_enable,
    input logic branch1_enable,
    input logic branch2_enable,
    input logic branch3_enable,
    input logic gsu_enable
);

    parameter [2:0] FEAT_MSU1 = 3,
                    FEAT_213F = 4,
                    FEAT_2100 = 6;

    // IS_ROM is the inverse of SNES_ROMSEL.
    check_is_rom: assert property (
        @(posedge CLK)
        IS_ROM == ~SNES_ROMSEL
    );

    // IS_SAVERAM matches the RTL decode expression.
    check_is_saveram: assert property (
        @(posedge CLK)
        IS_SAVERAM == (SAVERAM_MASK[0]
                       & ((&SNES_ADDR[22:21] & ~SNES_ROMSEL)
                          | (~SNES_ADDR[22] & ~SNES_ADDR[15] & &SNES_ADDR[14:13])))
    );

    // IS_WRITABLE always follows IS_SAVERAM.
    check_is_writable: assert property (
        @(posedge CLK)
        IS_WRITABLE == IS_SAVERAM
    );

    // ROM_ADDR uses the saveram address mapping when IS_SAVERAM is set.
    check_rom_addr_saveram_path: assert property (
        @(posedge CLK)
        IS_SAVERAM |-> (ROM_ADDR == (24'hE00000 + ((SNES_ADDR[22] ? SNES_ADDR[16:0] : SNES_ADDR[12:0]) & SAVERAM_MASK)))
    );

    // ROM_ADDR uses the ROM address mapping when IS_SAVERAM is clear.
    check_rom_addr_rom_path: assert property (
        @(posedge CLK)
        !IS_SAVERAM |-> (ROM_ADDR == ((SNES_ADDR[22] ? {2'b00, SNES_ADDR[21:0]} : {2'b00, SNES_ADDR[22:16], SNES_ADDR[14:0]}) & ROM_MASK))
    );

    // ROM_HIT is asserted for ROM or writable accesses.
    check_rom_hit: assert property (
        @(posedge CLK)
        ROM_HIT == (IS_ROM | IS_WRITABLE)
    );

    // msu_enable matches the feature bit and address decode.
    check_msu_enable: assert property (
        @(posedge CLK)
        msu_enable == (featurebits[FEAT_MSU1] & (!SNES_ADDR[22] && ((SNES_ADDR[15:0] & 16'hfff8) == 16'h2000)))
    );

    // r213f_enable matches the feature bit and page decode.
    check_r213f_enable: assert property (
        @(posedge CLK)
        r213f_enable == (featurebits[FEAT_213F] & (SNES_PA == 8'h3f))
    );

    // r2100_hit is high only for page 0x00.
    check_r2100_hit: assert property (
        @(posedge CLK)
        r2100_hit == (SNES_PA == 8'h00)
    );

    // snescmd_enable matches the address pattern decode.
    check_snescmd_enable: assert property (
        @(posedge CLK)
        snescmd_enable == ({SNES_ADDR[22], SNES_ADDR[15:9]} == 8'b0_0010101)
    );

    // nmicmd_enable matches the fixed address decode.
    check_nmicmd_enable: assert property (
        @(posedge CLK)
        nmicmd_enable == (SNES_ADDR == 24'h002BF2)
    );

    // return_vector_enable matches the fixed address decode.
    check_return_vector_enable: assert property (
        @(posedge CLK)
        return_vector_enable == (SNES_ADDR == 24'h002A6C)
    );

    // branch1_enable matches the fixed address decode.
    check_branch1_enable: assert property (
        @(posedge CLK)
        branch1_enable == (SNES_ADDR == 24'h002A1F)
    );

    // branch2_enable matches the fixed address decode.
    check_branch2_enable: assert property (
        @(posedge CLK)
        branch2_enable == (SNES_ADDR == 24'h002A59)
    );

    // branch3_enable matches the fixed address decode.
    check_branch3_enable: assert property (
        @(posedge CLK)
        branch3_enable == (SNES_ADDR == 24'h002A5E)
    );

    // gsu_enable matches the address range decode.
    check_gsu_enable: assert property (
        @(posedge CLK)
        gsu_enable == ((!SNES_ADDR[22] && ({SNES_ADDR[15:10], 2'h0} == 8'h30)) && (SNES_ADDR[9:8] != 2'h3))
    );

endmodule