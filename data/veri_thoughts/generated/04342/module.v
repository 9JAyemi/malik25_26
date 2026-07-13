
module top_module (
    input [3:0] A,
    input [3:0] B,
    input enable,
    output [3:0] result
);

    wire [1:0] comp_out;
    wire [15:0] dec_out;
    wire [3:0] final_out;

    // Instantiate the magnitude comparator module
    comparator comp_inst (
        .A(A),
        .B(B),
        .EQ(comp_out[0]),
        .GT(comp_out[1])
    );

    // Instantiate the 2-to-4 decoder module
    decoder dec_inst (
        .in(comp_out),
        .out(dec_out)
    );

    // Instantiate the functional module
    functional func_inst (
        .in(dec_out),
        .out(final_out)
    );

    // Output assignment based on the enable input
    assign result = enable ? final_out : 4'b0000;

endmodule
module comparator (
    input [3:0] A,
    input [3:0] B,
    output reg EQ,
    output reg GT
);

    always @ (A, B) begin
        if (A == B) begin
            EQ <= 1'b1;
            GT <= 1'b0;
        end else if (A > B) begin
            EQ <= 1'b0;
            GT <= 1'b1;
        end else begin
            EQ <= 1'b0;
            GT <= 1'b0;
        end
    end

endmodule
module decoder (
    input [1:0] in,
    output [15:0] out
);

    assign out = { 15'b0,
                   ~in[1] & ~in[0], // 00
                   ~in[1] & in[0],  // 01
                   in[1] & ~in[0],  // 10
                   in[1] & in[0]   // 11
                 };

endmodule
module functional (
    input [15:0] in,
    output reg [3:0] out
);

    always @ (in) begin
        case (in)
            16'b0000000000000010: out <= 4'b0001; // A < B
            16'b0000000000000100: out <= 4'b0010; // A = B
            16'b0000000000001000: out <= 4'b0100; // A > B
            default: out <= 4'b0000; // Invalid input
        endcase
    end

endmodule