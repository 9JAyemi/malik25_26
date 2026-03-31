module xor_gate (
    input a,
    input b,
    input clk,
    output reg out
);
    always @(posedge clk) begin
        out <= a ^ b;
    end
endmodule

module xnor_gate (
    input a,
    input b,
    output reg out
);
    always @(*) begin
        out = ~(a ^ b);
    end
endmodule

module mux_4to1 (
    input [3:0] in,
    input [1:0] sel,
    output reg out
);
    always @(*) begin
        case(sel)
            2'b00: out = in[0];
            2'b01: out = in[1];
            2'b10: out = in[2];
            2'b11: out = in[3];
        endcase
    end
endmodule

module top_module (
    input clk,
    input a,
    input b,
    output f
);
    wire xor_out;
    wire xnor_out;
    wire [3:0] mux_in;
    
    xor_gate xor_inst (
        .a(a),
        .b(b),
        .clk(clk),
        .out(xor_out)
    );
    
    xnor_gate xnor_inst (
        .a(a),
        .b(b),
        .out(xnor_out)
    );
    
    assign mux_in[0] = xor_out & xnor_out;
    assign mux_in[1] = ~xor_out & ~xnor_out;
    assign mux_in[2] = 1'b0;
    assign mux_in[3] = 1'b1;
    
    mux_4to1 mux_inst (
        .in(mux_in),
        .sel({xor_out, xnor_out}),
        .out(f)
    );
endmodule