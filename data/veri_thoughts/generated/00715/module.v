module byte_swap(
    input [31:0] in,
    output [31:0] out
);
    
    assign out = {in[7:0], in[15:8], in[23:16], in[31:24]};
    
endmodule

module xor_module(
    input [31:0] in,
    input [31:0] out,
    input enable,
    output [31:0] final_output
);
    
    assign final_output = enable ? (in ^ out) : 0;
    
endmodule

module top_module( 
    input [31:0] in,
    output [31:0] out,
    input enable,
    output [31:0] final_output
);
    
    byte_swap bs(in, out);
    xor_module xm(in, out, enable, final_output);
    
endmodule