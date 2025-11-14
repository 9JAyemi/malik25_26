module top_module (
    input clk,
    input reset,
    input [7:0] a,
    input [7:0] b,
    output [7:0] sum
);

    // D flip-flops to synchronize inputs
    reg [7:0] a_sync;
    reg [7:0] b_sync;
    always @(posedge clk) begin
        if (reset) begin
            a_sync <= 8'b0;
            b_sync <= 8'b0;
        end else begin
            a_sync <= a;
            b_sync <= b;
        end
    end

    // Ripple-carry adder
    wire [7:0] carry;
    full_adder fa0(a_sync[0], b_sync[0], 1'b0, sum[0], carry[0]);
    full_adder fa1(a_sync[1], b_sync[1], carry[0], sum[1], carry[1]);
    full_adder fa2(a_sync[2], b_sync[2], carry[1], sum[2], carry[2]);
    full_adder fa3(a_sync[3], b_sync[3], carry[2], sum[3], carry[3]);
    full_adder fa4(a_sync[4], b_sync[4], carry[3], sum[4], carry[4]);
    full_adder fa5(a_sync[5], b_sync[5], carry[4], sum[5], carry[5]);
    full_adder fa6(a_sync[6], b_sync[6], carry[5], sum[6], carry[6]);
    full_adder fa7(a_sync[7], b_sync[7], carry[6], sum[7], carry[7]);

endmodule

module full_adder (
    input A,
    input B,
    input C_in,
    output Sum,
    output C_out
);
    assign Sum = A ^ B ^ C_in;
    assign C_out = (A & B) | (C_in & (A ^ B));
endmodule