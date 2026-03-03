module zero_to_one_counter (
    input clk,
    input reset, // Synchronous active-high reset
    input [15:0] in, // 16-bit input
    output reg out // Output
);

    always @(posedge clk) begin
        if (reset) begin
            out <= 1'b0;
        end else if (in == 16'hFFFF) begin
            out <= 1'b1;
        end else begin
            out <= out + 1'b1;
        end
    end

endmodule

module adder_4bit_cin_cout (
    input [3:0] A, // 4-bit input A
    input [3:0] B, // 4-bit input B
    input CIN, // Carry-in
    output [3:0] S, // 4-bit output sum
    output COUT // Carry-out
);

    assign {COUT, S} = A + B + CIN;

endmodule

module top_module (
    input clk,
    input reset, // Synchronous active-high reset
    input [3:0] A, // 4-bit input for the adder
    input [3:0] B, // 4-bit input for the adder
    input CIN, // Carry-in for the adder
    input [15:0] in, // 16-bit input for the zero-to-one counter
    output [3:0] S // 4-bit output for the final sum
);

    wire [3:0] adder_out;
    wire zero_to_one_out;

    adder_4bit_cin_cout adder_inst (
        .A(A),
        .B(B),
        .CIN(CIN),
        .S(adder_out),
        .COUT()
    );

    zero_to_one_counter zero_to_one_inst (
        .clk(clk),
        .reset(reset),
        .in(in),
        .out(zero_to_one_out)
    );

    assign S = adder_out + zero_to_one_out;

endmodule