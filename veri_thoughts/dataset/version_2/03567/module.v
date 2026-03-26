
module top_module (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    input select,
    output [3:0] result,
    output wire eq,
    output wire gt,
    output wire lt
);

    wire [3:0] alu_result;

    alu_module alu_inst (
        .A(A),
        .B(B),
        .OP(OP),
        .result(alu_result)
    );

    comparator_module comparator_inst (
        .A(A),
        .B(B),
        .eq(eq),
        .gt(gt),
        .lt(lt)
    );

    assign result = select ? alu_result : 4'b0;

endmodule

module alu_module (
    input [3:0] A,
    input [3:0] B,
    input [2:0] OP,
    output reg [3:0] result
);

    always @(*) begin
        case (OP)
            3'b000: result = A + B;
            3'b001: result = A - B;
            3'b010: result = A & B;
            3'b011: result = A | B;
            3'b100: result = A ^ B;
            3'b101: result = {A[2:0], 1'b0};
            3'b110: result = A >> 1;
            3'b111: result = ~A;
        endcase
    end

endmodule

module comparator_module (
    input [3:0] A,
    input [3:0] B,
    output reg eq,
    output reg gt,
    output reg lt
);

    always @(*) begin
        eq = (A == B);
        gt = (A > B);
        lt = (A < B);
    end

endmodule
