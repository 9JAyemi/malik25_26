module ROM_A(
    input [31:0] addr,
    output [31:0] inst
);

    reg [31:0]instructions[128:0];
    
    initial begin
        // Initialize ROM with instructions
        instructions[0] = 32'h00000026;
        instructions[1] = 32'h00210826;
        instructions[2] = 32'h00421026;
        instructions[3] = 32'h00631826;
        instructions[4] = 32'h00842026;
        instructions[5] = 32'h00a52826;
        instructions[6] = 32'h00c63026;
        instructions[7] = 32'h00e73826;
        instructions[8] = 32'h01084026;
        instructions[9] = 32'h01294826;
        instructions[10] = 32'h014a5026;
        instructions[11] = 32'h016b5826;
        instructions[12] = 32'h018c6026;
        instructions[13] = 32'h01ad6826;
        instructions[14] = 32'h01ce7026;
        instructions[15] = 32'h01ef7826;
        instructions[16] = 32'h02108026;
        instructions[17] = 32'h02318826;
        instructions[18] = 32'h02529026;
        instructions[19] = 32'h02739826;
        instructions[20] = 32'h0294a026;
        instructions[21] = 32'h02b5a826;
        instructions[22] = 32'h02d6b026;
        instructions[23] = 32'h02f7b826;
        instructions[24] = 32'h0318c026;
        instructions[25] = 32'h0339c826;
        instructions[26] = 32'h035ad026;
        instructions[27] = 32'h037bd826;
        instructions[28] = 32'h039ce026;
        instructions[29] = 32'h03bde826;
        instructions[30] = 32'h03def026;
        instructions[31] = 32'h03fff826;
        instructions[32] = 32'h2108000a;
        instructions[33] = 32'h21290001;
        instructions[34] = 32'h214a0002;
        instructions[35] = 32'h216b0003;
        instructions[36] = 32'h218c0004;
        instructions[37] = 32'h21ad000a;
        instructions[38] = 32'h21ce000a;
        instructions[39] = 32'h21ef000a;
        instructions[40] = 32'h00892020;
        instructions[41] = 32'h00aa2820;
        instructions[42] = 32'h00cb3020;
        instructions[43] = 32'h00ec3820;
        instructions[44] = 32'h1488fffb;
        instructions[45] = 32'h22100001;
        instructions[46] = 32'h3c088000;
        instructions[47] = 32'h00008827;
        instructions[48] = 32'h00084042;
        instructions[49] = 32'h02119024;
        instructions[50] = 32'h01119825;
        instructions[51] = 32'h0111a026;
        instructions[52] = 32'h1408fffb;
        instructions[53] = 32'h3c1500ff;
        instructions[54] = 32'h22b500ff;
        instructions[55] = 32'hac150320;
        instructions[56] = 32'h8c160320;
        instructions[57] = 32'h12b60000;
        instructions[58] = 32'h00892022;
        instructions[59] = 32'h00aa2822;
        instructions[60] = 32'h00cb3022;
        instructions[61] = 32'h00ec3822;
        instructions[62] = 32'h00c0402a;
        instructions[63] = 32'h1008fffa;
        instructions[64] = 32'h0c000042;
        instructions[65] = 32'h08000000;
        instructions[66] = 32'h03e00008;
    end
    
    // Output the instruction at the specified address
    assign inst = instructions[addr];   

endmodule