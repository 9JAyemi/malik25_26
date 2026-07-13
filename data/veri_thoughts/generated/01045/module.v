
module add_sub_comp (
    input [3:0] a,
    input [3:0] b,
    input sub,
    output reg out
);

    reg [3:0] result;
    wire [1:0] comp_out;
    
    two_bit_comparator comp (
        .a(a),       // Fix the a and b inputs order
        .b(b),   // Fix the a and b inputs order
        .out(comp_out)
    );

    adder_subtractor add_sub (
        .a(a),
        .b(b),
        .sub(sub),
        .result(result)
    );
    
    always @(*) begin
        case (comp_out)
            2'b00: out <= 1;
            default: out <= 0;
        endcase
    end
    
endmodule
module two_bit_comparator (
    input [3:0] a,
    input [3:0] b,
    output reg [1:0] out
);

    always @(*) begin
        if (a > b) begin
            out = 2'b10;
        end else if (a == b) begin
            out = 2'b01;
        end else begin
            out = 2'b00;
        end
    end
    
endmodule
module adder_subtractor (
    input [3:0] a,
    input [3:0] b,
    input sub,
    output reg [3:0] result
);

    always @(*) begin
        if (sub) begin
            result = a - b;
        end else begin
            result = a + b;
        end
    end

endmodule