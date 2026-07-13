module top_module (
    input [3:0] A, B,
    input [2:0] OP,
    input [3:0] a, b,
    output [1:0] final_output
);

    wire [3:0] alu_result;
    wire [2:0] comparison_result;
    
    alu alu_inst (
        .A(A),
        .B(B),
        .OP(OP),
        .P(alu_result)
    );
    
    mag_comp_priority_encoder mag_comp_inst (
        .a(a),
        .b(b),
        .comparison_result(comparison_result)
    );
    
    assign final_output = (comparison_result == 3 && alu_result == 0) ? 2'b10 :
                          (comparison_result == 2) ? 2'b01 :
                          (comparison_result == 1) ? 2'b00 :
                          2'b11;

endmodule

module alu (
    input [3:0] A, B,
    input [2:0] OP,
    output reg [3:0] P
);

    always @(*) begin
        case (OP)
            3'b000: P = A & B;
            3'b001: P = A | B;
            3'b010: P = A + B;
            3'b011: P = A - B;
            3'b100: P = A ^ B;
            3'b101: P = ~A;
            3'b110: P = A << 1;
            3'b111: P = A >> 1;
            default: P = 4'bxxxx;
        endcase
    end

endmodule

module mag_comp_priority_encoder (
    input [3:0] a, b,
    output reg [2:0] comparison_result
);

    always @(*) begin
        if (a > b) begin
            comparison_result = 3'b010;
        end else if (a < b) begin
            comparison_result = 3'b001;
        end else begin
            comparison_result = 3'b000;
        end
    end

endmodule