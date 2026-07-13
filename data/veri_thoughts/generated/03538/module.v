
module top_module (
    input [3:0] A,
    input [3:0] B,
    input C,
    input select,
    output reg [3:0] out
);

    wire [3:0] adder_out;
    wire [3:0] twos_comp_out;

    // Instantiate the adder/subtractor module
    add_sub_4bit add_sub_inst (
        .A(A),
        .B(B),
        .C(C),
        .out(adder_out)
    );

    // Instantiate the two's complement converter module
    twos_comp_4bit twos_comp_inst (
        .in(adder_out),
        .out(twos_comp_out)
    );

    // Functional module to choose between adder/subtractor and two's complement converter
    always @(*) begin
        if (select) begin
            out <= twos_comp_out;
        end else begin
            out <= adder_out;
        end
    end

endmodule
module twos_comp_4bit (
    input [3:0] in,
    output reg [3:0] out
);

    always @(*) begin
        out <= ~in + 1'b1;
    end

endmodule
module add_sub_4bit (
    input [3:0] A,
    input [3:0] B,
    input C,
    output reg [3:0] out
);

    always @(*) begin
        if (C) begin
            out <= A + B;
        end else begin
            out <= A - B;
        end
    end

endmodule