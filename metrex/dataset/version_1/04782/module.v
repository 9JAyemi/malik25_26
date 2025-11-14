
module zybo_top 
    (
        // Main clock. See @note1.
        input               CLK_125MHZ_I,
        // Various I/O ports connected to board devices.
        input        [3:0]  BUTTONS_I,
        input        [3:0]  SWITCHES_I,
        output reg   [3:0]  LEDS_O,
        // PMOD E (Std) connector -- PMOD UART (Digilent).
        output reg          PMOD_E_2_TXD_O,
        input               PMOD_E_3_RXD_I
    ); 

    reg [31:0] bogoinput;
    reg [31:0] dbg_out;
    reg [31:0] dbg_in;
    reg reset;

    //RV32ICore mcu_inst (
    // Size of Code TCM in 32-bit words.
    //.OPTION_CTCM_NUM_WORDS(1024),
    // Main clock. See @note1.
    //.CLK            (CLK_125MHZ_I),
    // Reset.
    //.RESET_I        (reset),

    //.DEBUG_I        (dbg_in),
    //.DEBUG_O        (dbg_out) 
    //); 

    always @(*) begin
        LEDS_O = dbg_out[31:28] ^ dbg_out[27:24] ^ dbg_out[23:20] ^ dbg_out[19:16] ^
                  dbg_out[15:12] ^ dbg_out[11: 8] ^ dbg_out[ 7: 4] ^ dbg_out[ 3: 0];

        reset = |BUTTONS_I;

        PMOD_E_2_TXD_O = PMOD_E_3_RXD_I;
    end

    always @(posedge CLK_125MHZ_I) begin
        if (reset) begin
            bogoinput <= 32'h0;
            dbg_out <= 32'h0;
            dbg_in <= 32'h0;
        end
        else begin 
            bogoinput <= {SWITCHES_I, {24{1'b0}}};
            dbg_in <= dbg_out + bogoinput;    // Fix #1: Drive dbg_in
            dbg_out <= dbg_out + bogoinput;    // Fix #2: Drive dbg_out
        end 
    end    

endmodule