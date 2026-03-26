module memmap(

    input a15, a14, // Z80 address signals

    input mreq_n, rd_n, wr_n, // Z80 bus control signals

    input mode_ramro, mode_norom, // control signals for read-only memory and ROM mode, respectively

    input [7:0] mode_pg0, mode_pg1, mode_pg2, mode_pg3, // page select signals for the lower 16KB of memory

    output reg mema14, mema15, mema16, mema17, mema18, mema21, // memory address signals

    output reg ram0cs_n, ram1cs_n, ram2cs_n, ram3cs_n, // chip select signals for the four RAM chips

    output reg romcs_n, // chip select signal for the ROM chip

    output reg memoe_n, memwe_n // memory control signals

);

    // internal vars and regs

    reg [7:0] high_addr;

    // addresses mapping

    always @*
    begin
        case( {a15,a14} )
            2'b00: // $0000-$3FFF
                high_addr <= mode_pg0;
            2'b01: // $4000-$7FFF
                high_addr <= mode_pg1;
            2'b10: // $8000-$BFFF
                high_addr <= mode_pg2;
            2'b11: // $C000-$FFFF
                high_addr <= mode_pg3;
        endcase
    end

    // memory addresses

    always @*
    begin
        { mema21, mema18, mema17, mema16, mema15, mema14 } <= { high_addr[7], high_addr[4:0] };
    end

    // memory chip selects

    always @*
    begin
        if( (mode_norom==1'b0) && ( {a15,a14}!=2'b01 ) ) // ROM selected
        begin
            romcs_n <= 1'b0;

            ram0cs_n <= 1'b1;
            ram1cs_n <= 1'b1;
            ram2cs_n <= 1'b1;
            ram3cs_n <= 1'b1;
        end
        else // RAM
        begin
            romcs_n <= 1'b1;

            ram0cs_n <= ( high_addr[6:5]==2'b00 ) ? 1'b0 : 1'b1;
            ram1cs_n <= ( high_addr[6:5]==2'b01 ) ? 1'b0 : 1'b1;
            ram2cs_n <= ( high_addr[6:5]==2'b10 ) ? 1'b0 : 1'b1;
            ram3cs_n <= ( high_addr[6:5]==2'b11 ) ? 1'b0 : 1'b1;
        end
    end

    // memory /OE and /WE

    always @*
    begin
        memoe_n <= mreq_n | rd_n;

        if( (high_addr[6:1] == 6'd0) && (mode_ramro==1'b1) && (mode_norom==1'b1) ) // R/O
            memwe_n <= 1'b1;
        else // no R/O
            memwe_n <= mreq_n | wr_n;
    end

endmodule