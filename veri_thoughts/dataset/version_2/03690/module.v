module top_module (
    input [15:0] in,
    input [3:0] sel,
    input EN,
    input [3:0] A,
    input [3:0] B,
    input [2:0] op,
    output reg [3:0] out,
    output reg valid
);

reg [3:0] mux_out;
reg [3:0] alu_out;

// 16-to-1 multiplexer
always @(*) begin
    case(sel)
        4'd0: mux_out = in[3:0];
        4'd1: mux_out = in[7:4];
        4'd2: mux_out = in[11:8];
        4'd3: mux_out = in[15:12];
        default: mux_out = 4'b0;
    endcase
end

// 4-bit ALU
always @(*) begin
    case(op)
        3'b000: alu_out = A + B;
        3'b001: alu_out = A - B;
        3'b010: alu_out = A & B;
        3'b011: alu_out = A | B;
        3'b100: alu_out = A ^ B;
        default: alu_out = 4'b0;
    endcase
end

// Final output module
always @(*) begin
    if(valid) begin
        out = alu_out;
    end else if(EN) begin
        out = mux_out;
    end else begin
        out = 4'b0;
    end
    
    valid = (op != 3'b101);
end

endmodule