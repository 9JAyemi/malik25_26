
module conditional_output (
    input [3:0] A,
    input [3:0] B,
    input [1:0] C,
    output wire [3:0] out
);
    assign out = (C == 2'b00)? A : (C == 2'b01)? B : (C == 2'b10)? A ^ B : 4'b0;
endmodule

module up_down_counter (
    input CLK,
    input UP_DOWN,
    output reg [2:0] Q
);
    always @(posedge CLK) begin
        if (UP_DOWN == 1'b1) begin
            if (Q == 3'b111) begin
                Q <= 3'b000;
            end else begin
                Q <= Q + 1'b1;
            end
        end else begin
            if (Q == 3'b000) begin
                Q <= 3'b111;
            end else begin
                Q <= Q - 1'b1;
            end
        end
    end
endmodule

module sum_module (
    input [3:0] A,
    input [3:0] B,
    input [2:0] counter,
    output wire [7:0] out
);
    assign out = {A, B} + counter;
endmodule

module top_module (
    input CLK,
    input reset,
    input [3:0] A,
    input [3:0] B,
    input [1:0] C,
    input UP_DOWN,
    output wire [7:0] out
);
    wire [3:0] conditional_output_result;
    wire [2:0] up_down_counter_result;

    conditional_output conditional_output_inst (
        .A(A),
        .B(B),
        .C(C),
        .out(conditional_output_result)
    );

    up_down_counter up_down_counter_inst (
        .CLK(CLK),
        .UP_DOWN(UP_DOWN),
        .Q(up_down_counter_result)
    );

    sum_module sum_module_inst (
        .A(conditional_output_result),
        .B({1'b0, up_down_counter_result}),
        .counter(up_down_counter_result),
        .out(out)
    );

endmodule
