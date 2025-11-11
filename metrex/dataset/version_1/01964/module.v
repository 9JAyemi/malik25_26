
module shift_reg_mux_adder (
    input         clk,
    input         d,
    input  [255:0] in,
    input   [7:0] sel,
    output reg out
);

    reg [2:0] shift_reg;
    reg [7:0] shifted_in;
    wire [7:0] mux_out;
    wire       reg_out;
    
    // Shift register
    always @(posedge clk) begin
        shift_reg <= {shift_reg[1:0], d};
    end
    
    // Barrel shifter
    always @(*) begin
        case (sel)
            8'h00: shifted_in = in[7:0];
            8'h01: shifted_in = in[15:8];
            8'h02: shifted_in = in[23:16];
            8'h03: shifted_in = in[31:24];
            8'h04: shifted_in = in[39:32];
            8'h05: shifted_in = in[47:40];
            8'h06: shifted_in = in[55:48];
            8'h07: shifted_in = in[63:56];
            8'h08: shifted_in = in[71:64];
            8'h09: shifted_in = in[79:72];
            8'h0A: shifted_in = in[87:80];
            8'h0B: shifted_in = in[95:88];
            8'h0C: shifted_in = in[103:96];
            8'h0D: shifted_in = in[111:104];
            8'h0E: shifted_in = in[119:112];
            8'h0F: shifted_in = in[127:120];
            8'h10: shifted_in = in[135:128];
            8'h11: shifted_in = in[143:136];
            8'h12: shifted_in = in[151:144];
            8'h13: shifted_in = in[159:152];
            8'h14: shifted_in = in[167:160];
            8'h15: shifted_in = in[175:168];
            8'h16: shifted_in = in[183:176];
            8'h17: shifted_in = in[191:184];
            8'h18: shifted_in = in[199:192];
            8'h19: shifted_in = in[207:200];
            8'h1A: shifted_in = in[215:208];
            8'h1B: shifted_in = in[223:216];
            8'h1C: shifted_in = in[231:224];
            8'h1D: shifted_in = in[239:232];
            8'h1E: shifted_in = in[247:240];
            8'h1F: shifted_in = in[255:248];
            default: shifted_in = 8'h00;
        endcase
    end
    
    // Multiplexer
    assign mux_out = shifted_in;
    
    // 4-to-1 multiplexer
    assign reg_out = mux_out[shift_reg[2:0]];
    
    // Adder
    always @(*) begin
        out = reg_out + shift_reg[2];
    end
    
endmodule