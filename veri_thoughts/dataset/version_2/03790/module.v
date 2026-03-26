module top_module( 
    input clk,
    input [3:0] a,
    input [3:0] b,
    input d,
    output [3:0] out_nand_bitwise,
    output out_nand_logical,
    output [3:0] out_xor_bitwise,
    output out_xor_logical,
    output q
);

    // Logical Operations Module
    wire [3:0] nand_bitwise;
    wire nand_logical;
    wire [3:0] xor_bitwise;
    wire xor_logical;
    
    nand_4bit nand_inst(
        .a(a),
        .b(b),
        .out(nand_bitwise)
    );
    
    nand_logical_4bit nand_logical_inst(
        .a(a),
        .b(b),
        .out(nand_logical)
    );
    
    xor_4bit xor_inst(
        .a(a),
        .b(b),
        .out(xor_bitwise)
    );
    
    xor_logical_4bit xor_logical_inst(
        .a(a),
        .b(b),
        .out(xor_logical)
    );
    
    // Shift Register
    reg [3:0] shift_reg;
    
    always @(posedge clk) begin
        shift_reg <= {shift_reg[2:0], d};
    end
    
    // Functional Module
    assign out_nand_bitwise = nand_bitwise;
    assign out_nand_logical = nand_logical;
    assign out_xor_bitwise = xor_bitwise;
    assign out_xor_logical = xor_logical;
    assign q = shift_reg[3] & (nand_logical & shift_reg[0] & shift_reg[1] & shift_reg[2]);
    
endmodule

module nand_4bit(
    input [3:0] a,
    input [3:0] b,
    output [3:0] out
);
    
    assign out = ~(a & b);
    
endmodule

module nand_logical_4bit(
    input [3:0] a,
    input [3:0] b,
    output out
);
    
    assign out = ~(a & b) == 4'b1111;
    
endmodule

module xor_4bit(
    input [3:0] a,
    input [3:0] b,
    output [3:0] out
);
    
    assign out = a ^ b;
    
endmodule

module xor_logical_4bit(
    input [3:0] a,
    input [3:0] b,
    output out
);
    
    assign out = (a ^ b) == 4'b0000;
    
endmodule