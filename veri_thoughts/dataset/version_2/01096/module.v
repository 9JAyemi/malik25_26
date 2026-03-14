
module top_module (
    input [3:0] A,
    input [3:0] B,
    input SUBTRACT,
    output reg [3:0] SUM,
    output reg OVERFLOW,
    output reg EQUAL,
    output reg GREATER_THAN,
    output reg LESS_THAN
);

    wire [3:0] add_sub_out;
    wire [1:0] comp_out;
    reg overflow_int;

    reg carry_in;
    
    adder_subtractor add_sub (
        .A(A),
        .B(B),
        .SUBTRACT(SUBTRACT),
        .OUT(add_sub_out),
        .OVERFLOW(overflow_int)
    );
    
    comparator_2bit comp (
        .A(A),
        .B(B),
        .OUT(comp_out)
    );
    
    always @* begin
        SUM <= add_sub_out;
        OVERFLOW <= overflow_int;
        EQUAL <= (comp_out == 2'b01);
        GREATER_THAN <= (comp_out == 2'b10);
        LESS_THAN <= (comp_out == 2'b00);
    end
endmodule
module adder_subtractor (
    input [3:0] A,
    input [3:0] B,
    input SUBTRACT,
    output reg [3:0] OUT,
    output reg OVERFLOW
);

    wire [3:0] twos_comp_B = (~B) + 1;
    
    always @* begin
        OUT <= A;
        OVERFLOW <= 0;
        if (SUBTRACT) begin
            OUT <= A + twos_comp_B;
        end else begin
            OUT <= A + B;
        end
        if (A >= OUT && SUBTRACT) begin
            OVERFLOW <= 1;
        end else if (A <= OUT && !SUBTRACT) begin
            OVERFLOW <= 1;
        end
    end
endmodule
module comparator_2bit (
    input [3:0] A,
    input [3:0] B,
    output reg [1:0] OUT
);

    always @(*) begin
        if (A > B) begin
            OUT <= 2'b10;
        end else if (A < B) begin
            OUT <= 2'b00;
        end else begin
            OUT <= 2'b01;
        end
    end
endmodule