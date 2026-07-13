
module shift_addsub (
    input clk,
    input reset,
    input SER,
    input [3:0] A,
    input [3:0] B,
    input sub,
    output [3:0] result
);

    reg [3:0] Q;
    wire [3:0] shifted_Q;
    wire [3:0] added_A;
    wire [3:0] subbed_A;

    shift_register shift_reg (
        .clk(clk),
        .reset(reset),
        .SER(SER),
        .SHIFT(shifted_Q),
        .LOAD(Q)
    );

    adder_subtractor addsub (
        .A(A),
        .B(shifted_Q),
        .sub(sub),
        .result(added_A),
        .sub_result(subbed_A)
    );

    always @(posedge clk or posedge reset)
    begin
        if (reset)
            Q <= 4'b0;
        else
            Q <= subbed_A;
    end

    assign result = (sub) ? subbed_A : added_A;

endmodule
module shift_register (
    input clk,
    input reset,
    input SER,
    output reg [3:0] SHIFT,
    input [3:0] LOAD
);

    always @(posedge clk or posedge reset) begin
        if (reset) begin
            SHIFT <= 4'b0;
        end else begin
            SHIFT <= LOAD;
        end
    end

endmodule
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input sub,
    output [3:0] result,
    output [3:0] sub_result
);

    wire [3:0] subbed_A;
    wire [3:0] subtracted_result;

    assign subbed_A = (~A) + 1;
    assign subtracted_result = subbed_A + B;

    assign sub_result = subtracted_result[3:0];
    assign result = sub ? subtracted_result[3:0] : A + B;
endmodule