
module f1_TECH_AND18(input [17:0] in, output out);
assign out = &in;
endmodule

module f1_TECH_AND4(input [3:0] in, output out);
assign out = &in;
endmodule

module f2_TECH_AND5(input [4:0] in, output out);
assign out = &in;
endmodule

module f3_TECH_NAND18(input [17:0] in, output out);
assign out = ~(&in);
endmodule

module f3_TECH_NAND4(input [3:0] in, output out);
assign out = ~(&in);
endmodule

module f3_TECH_NAND2(input [1:0] in, output out);
assign out = ~(&in);
endmodule

module f4_TECH_NAND18(input [17:0] in, output out);
assign out = ~(&in);
endmodule

module f4_TECH_NAND4(input [3:0] in, output out);
assign out = ~(&in);
endmodule

module f4_TECH_NAND2(input [1:0] in, output out);
assign out = ~(&in);
endmodule

module f5_TECH_NAND18(input [17:0] in, output out);
assign out = ~(&in);
endmodule

module f5_TECH_NAND4(input [3:0] in, output out);
assign out = ~(&in);
endmodule

module f5_TECH_NAND2(input [1:0] in, output out);
assign out = ~(&in);
endmodule

module f6_TECH_NOR18(input [17:0] in, output out);
assign out = ~(|in);
endmodule

module f6_TECH_NOR4(input [3:0] in, output out);
assign out = ~(|in);
endmodule

module f6_TECH_NOR2(input [1:0] in, output out);
assign out = ~(|in);
endmodule

module f7_TECH_NOR18(input [17:0] in, output out);
assign out = ~(|in);
endmodule

module f7_TECH_NOR4(input [3:0] in, output out);
assign out = ~(|in);
endmodule

module f7_TECH_NOR2(input [1:0] in, output out);
assign out = ~(|in);
endmodule

module f8_TECH_NOR18(input [17:0] in, output out);
assign out = ~(|in);
endmodule

module f8_TECH_NOR4(input [3:0] in, output out);
assign out = ~(|in);
endmodule

module f8_TECH_NOR2(input [1:0] in, output out);
assign out = ~(|in);
endmodule

module f9_TECH_OR18(input [17:0] in, output out);
assign out = |in;
endmodule

module f9_TECH_OR4(input [3:0] in, output out);
assign out = |in;
endmodule

module f10_TECH_OR5(input [4:0] in, output out);
assign out = |in;
endmodule

module f11_TECH_XOR5(input [4:0] in, output out);
assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4];
endmodule
module f11_TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule

module f12_TECH_XOR5(input [4:0] in, output out);
assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4];
endmodule
module f12_TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule

module f13_TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule

module f14_TECH_XOR5(input [4:0] in, output out);
assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4];
endmodule
module f14_TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule

module f15_TECH_XOR5(input [4:0] in, output out);
assign out = in[0] ^ in[1] ^ in[2] ^ in[3] ^ in[4];
endmodule
module f15_TECH_XOR2(input [1:0] in, output out);
assign out = in[0] ^ in[1];
endmodule
