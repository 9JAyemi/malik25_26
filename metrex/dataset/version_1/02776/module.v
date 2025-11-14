
module mult_16x16 (
    input [15:0] Amult, // o
    input [15:0] Bmult, // o
    input [1:0] Valid_mult, // o
    output [31:0] Cmult // i
);

    wire [31:0] Amult_int;
    wire [31:0] Bmult_int;
    wire [63:0] Cmult_int;

    assign Amult_int = {16'b0, Amult};
    assign Bmult_int = {16'b0, Bmult};

    MULT #(.WIDTH(32)) mult_inst (
        .Amult(Amult_int), // i
        .Bmult(Bmult_int), // i
        .Valid_mult(Valid_mult), // i
        .Cmult(Cmult_int), // o
        .sel_mul_32x32(1'b1) // i
    );

    assign Cmult = Cmult_int[31:0];

endmodule
module MULT #(
    parameter WIDTH = 32
) (
    input [WIDTH-1:0] Amult, // i
    input [WIDTH-1:0] Bmult, // i
    input [1:0] Valid_mult, // i
    output [2*WIDTH-1:0] Cmult, // o
    input sel_mul_32x32 // i
);

    reg [2*WIDTH-1:0] Cmult_reg;
    reg [WIDTH-1:0] Amult_reg;
    reg [WIDTH-1:0] Bmult_reg;
    reg [1:0] Valid_mult_reg;

    always @(posedge Valid_mult[0]) begin
        Amult_reg <= Amult;
        Bmult_reg <= Bmult;
        Valid_mult_reg <= Valid_mult;
    end

    always @(posedge Valid_mult[0]) begin
        if (sel_mul_32x32) begin
            Cmult_reg <= Amult_reg * Bmult_reg;
        end else begin
            Cmult_reg <= {WIDTH{1'b0}};
        end
    end

    assign Cmult = Cmult_reg;

endmodule