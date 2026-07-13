module memmap_sva(
    input logic a15,
    input logic a14,
    input logic mreq_n,
    input logic rd_n,
    input logic wr_n,
    input logic mode_ramro,
    input logic mode_norom,
    input logic [7:0] mode_pg0,
    input logic [7:0] mode_pg1,
    input logic [7:0] mode_pg2,
    input logic [7:0] mode_pg3,
    input logic mema14,
    input logic mema15,
    input logic mema16,
    input logic mema17,
    input logic mema18,
    input logic mema21,
    input logic ram0cs_n,
    input logic ram1cs_n,
    input logic ram2cs_n,
    input logic ram3cs_n,
    input logic romcs_n,
    input logic memoe_n,
    input logic memwe_n
);

    function automatic logic [7:0] selected_page(
        input logic a15_i,
        input logic a14_i,
        input logic [7:0] pg0_i,
        input logic [7:0] pg1_i,
        input logic [7:0] pg2_i,
        input logic [7:0] pg3_i
    );
        begin
            case ({a15_i, a14_i})
                2'b00: selected_page = pg0_i;
                2'b01: selected_page = pg1_i;
                2'b10: selected_page = pg2_i;
                default: selected_page = pg3_i;
            endcase
        end
    endfunction

    function automatic logic [5:0] expected_mema(
        input logic a15_i,
        input logic a14_i,
        input logic [7:0] pg0_i,
        input logic [7:0] pg1_i,
        input logic [7:0] pg2_i,
        input logic [7:0] pg3_i
    );
        logic [7:0] page;
        begin
            page = selected_page(a15_i, a14_i, pg0_i, pg1_i, pg2_i, pg3_i);
            expected_mema = {page[7], page[4:0]};
        end
    endfunction

    function automatic logic [1:0] expected_ram_bank(
        input logic a15_i,
        input logic a14_i,
        input logic [7:0] pg0_i,
        input logic [7:0] pg1_i,
        input logic [7:0] pg2_i,
        input logic [7:0] pg3_i
    );
        logic [7:0] page;
        begin
            page = selected_page(a15_i, a14_i, pg0_i, pg1_i, pg2_i, pg3_i);
            expected_ram_bank = page[6:5];
        end
    endfunction

    function automatic logic rom_path_selected(
        input logic a15_i,
        input logic a14_i,
        input logic mode_norom_i
    );
        begin
            rom_path_selected = (mode_norom_i == 1'b0) && ({a15_i, a14_i} != 2'b01);
        end
    endfunction

    function automatic logic ro_block_active(
        input logic a15_i,
        input logic a14_i,
        input logic mode_ramro_i,
        input logic mode_norom_i,
        input logic [7:0] pg0_i,
        input logic [7:0] pg1_i,
        input logic [7:0] pg2_i,
        input logic [7:0] pg3_i
    );
        logic [7:0] page;
        begin
            page = selected_page(a15_i, a14_i, pg0_i, pg1_i, pg2_i, pg3_i);
            ro_block_active = (page[6:1] == 6'd0) && (mode_ramro_i == 1'b1) && (mode_norom_i == 1'b1);
        end
    endfunction

    // Checks memory address outputs use the selected page bits.
    check_mema_mapping: assert property (
        @($global_clock)
        {mema21, mema18, mema17, mema16, mema15, mema14} ==
        expected_mema(a15, a14, mode_pg0, mode_pg1, mode_pg2, mode_pg3)
    );

    // Checks ROM path forces ROM active and all RAM chips inactive.
    check_rom_select: assert property (
        @($global_clock)
        rom_path_selected(a15, a14, mode_norom) |->
        ((romcs_n == 1'b0) &&
         (ram0cs_n == 1'b1) &&
         (ram1cs_n == 1'b1) &&
         (ram2cs_n == 1'b1) &&
         (ram3cs_n == 1'b1))
    );

    // Checks ROM stays inactive whenever the RAM path is selected.
    check_rom_deselected_in_ram_path: assert property (
        @($global_clock)
        (!rom_path_selected(a15, a14, mode_norom)) |->
        (romcs_n == 1'b1)
    );

    // Checks RAM0 select decodes bank 00 on the RAM path.
    check_ram0_decode: assert property (
        @($global_clock)
        (!rom_path_selected(a15, a14, mode_norom)) |->
        (ram0cs_n == ((expected_ram_bank(a15, a14, mode_pg0, mode_pg1, mode_pg2, mode_pg3) == 2'b00) ? 1'b0 : 1'b1))
    );

    // Checks RAM1 select decodes bank 01 on the RAM path.
    check_ram1_decode: assert property (
        @($global_clock)
        (!rom_path_selected(a15, a14, mode_norom)) |->
        (ram1cs_n == ((expected_ram_bank(a15, a14, mode_pg0, mode_pg1, mode_pg2, mode_pg3) == 2'b01) ? 1'b0 : 1'b1))
    );

    // Checks RAM2 select decodes bank 10 on the RAM path.
    check_ram2_decode: assert property (
        @($global_clock)
        (!rom_path_selected(a15, a14, mode_norom)) |->
        (ram2cs_n == ((expected_ram_bank(a15, a14, mode_pg0, mode_pg1, mode_pg2, mode_pg3) == 2'b10) ? 1'b0 : 1'b1))
    );

    // Checks RAM3 select decodes bank 11 on the RAM path.
    check_ram3_decode: assert property (
        @($global_clock)
        (!rom_path_selected(a15, a14, mode_norom)) |->
        (ram3cs_n == ((expected_ram_bank(a15, a14, mode_pg0, mode_pg1, mode_pg2, mode_pg3) == 2'b11) ? 1'b0 : 1'b1))
    );

    // Checks /OE is the OR of MREQ and RD.
    check_memoe_decode: assert property (
        @($global_clock)
        memoe_n == (mreq_n | rd_n)
    );

    // Checks read-only pages block writes when RAM R/O mode is enabled.
    check_memwe_ro_block: assert property (
        @($global_clock)
        ro_block_active(a15, a14, mode_ramro, mode_norom, mode_pg0, mode_pg1, mode_pg2, mode_pg3) |->
        (memwe_n == 1'b1)
    );

    // Checks /WE otherwise follows the OR of MREQ and WR.
    check_memwe_decode: assert property (
        @($global_clock)
        (!ro_block_active(a15, a14, mode_ramro, mode_norom, mode_pg0, mode_pg1, mode_pg2, mode_pg3)) |->
        (memwe_n == (mreq_n | wr_n))
    );

endmodule