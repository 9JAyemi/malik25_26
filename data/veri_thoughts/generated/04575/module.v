
module alu (
    input [3:0] A,
    input [3:0] B,
    input [2:0] op,
    output [3:0] Z
);

    reg [3:0] temp;

    always @(*) begin
        case (op)
            3'b000: temp = A + B;
            3'b001: temp = A - B;
            3'b010: temp = A & B;
            3'b011: temp = A | B;
            3'b100: temp = A ^ B;
            3'b101: temp = ~A;
            default: temp = 4'b0;
        endcase
    end

    assign Z = temp;

endmodule

module shift_register (
    input clk,
    input LOAD,
    input SHIFT,
    input [7:0] DATA_IN,
    output reg [3:0] Q_OUT,
    output reg [3:0] Q_BAR_OUT
);

    always @(posedge clk) begin
        if (LOAD) begin
            Q_OUT <= DATA_IN[3:0];
            Q_BAR_OUT <= ~DATA_IN[3:0];
        end else if (SHIFT) begin
            Q_OUT <= {Q_OUT[2:0], 1'b0};
            Q_BAR_OUT <= {Q_BAR_OUT[2:0], 1'b1};
        end
    end

endmodule

module final_module (
    input [3:0] A,
    input [3:0] B,
    input [7:0] DATA_IN,
    input LOAD,
    input SHIFT,
    input [2:0] op,
    input clk,
    input reset,
    output reg [3:0] Z
);

    wire [3:0] alu_out;
    wire [3:0] shift_out;
    wire [3:0] and_out;

    alu alu_inst (
        .A(A),
        .B(B),
        .op(op),
        .Z(alu_out)
    );

    shift_register shift_inst (
        .clk(clk),
        .LOAD(LOAD),
        .SHIFT(SHIFT),
        .DATA_IN(DATA_IN),
        .Q_OUT(shift_out),
        .Q_BAR_OUT()
    );

    assign and_out = alu_out & shift_out;

    always @(posedge clk) begin
        if (reset) begin
            Z <= 4'b0;
        end else begin
            Z <= and_out;
        end
    end

endmodule

module top_module (
    input clk,
    input reset,      // Synchronous active-high reset
    input [3:0] A,    // 4-bit input for ALU
    input [3:0] B,    // 4-bit input for ALU
    input [2:0] op,   // 3-bit control input for ALU
    input [7:0] DATA_IN,  // 8-bit input for shift register
    input LOAD,       // Input to load DATA_IN into shift register
    input SHIFT,      // Input to shift contents of shift register
    output [3:0] Z    // 4-bit output from ALU
);

    final_module final_inst (
        .A(A),
        .B(B),
        .op(op),
        .DATA_IN(DATA_IN),
        .LOAD(LOAD),
        .SHIFT(SHIFT),
        .clk(clk),
        .reset(reset),
        .Z(Z)
    );

endmodule
