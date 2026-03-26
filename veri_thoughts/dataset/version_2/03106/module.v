
module top_module (
    input [3:0] A,
    input [3:0] B,
    input [7:0] C,
    output [7:0] final_output
);

    wire [7:0] multiplier_output;
    wire [1:0] comparator_output;
    
    multiplier mult(A, B, multiplier_output);
    mag_comparator comp(multiplier_output, C, comparator_output);
    functional_module func(multiplier_output, comparator_output, final_output);

endmodule
module multiplier (
    input [3:0] A,
    input [3:0] B,
    output [7:0] product
);

    assign product = {4'b0, A} * {4'b0, B};

endmodule
module mag_comparator (
    input [7:0] comp_input,
    input [7:0] C,
    output reg [1:0] result
);

    always @(*) begin
        if (comp_input == C) begin
            result = 2'b00;
        end else if (comp_input > C) begin
            result = 2'b01;
        end else begin
            result = 2'b10;
        end
    end

endmodule
module functional_module (
    input [7:0] multiplier_output,
    input [1:0] comparator_output,
    output [7:0] final_output
);

    assign final_output = multiplier_output + {2'b0, comparator_output};

endmodule