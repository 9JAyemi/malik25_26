module sbox64(addr, dout);
input [5:0] addr;
output [3:0] dout;

reg [3:0] dout;

always @(addr) begin
    case (addr)
        6'h00: dout = 4'h0E;
        6'h01: dout = 4'h04;
        6'h02: dout = 4'h0D;
        6'h03: dout = 4'h01;
        6'h04: dout = 4'h02;
        6'h05: dout = 4'h0F;
        6'h06: dout = 4'h0B;
        6'h07: dout = 4'h08;
        6'h08: dout = 4'h03;
        6'h09: dout = 4'h0A;
        6'h0A: dout = 4'h06;
        6'h0B: dout = 4'h0C;
        6'h0C: dout = 4'h05;
        6'h0D: dout = 4'h09;
        6'h0E: dout = 4'h00;
        6'h0F: dout = 4'h07;
        default: dout = 4'h00;
    endcase
end

endmodule