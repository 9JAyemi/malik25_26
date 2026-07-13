
module comparator (
    input [3:0] in0,
    input [3:0] in1,
    output reg result
);

always @(*) begin
    result = (in0 > in1);
end

endmodule

module binary_to_bcd (
    input [3:0] B,
    output reg [3:0] D,
    output reg [3:0] C
);

always @(*) begin
    case (B)
        4'b0000: begin
            D = 4'b0000;
            C = 4'b0000;
        end
        4'b0001: begin
            D = 4'b0000;
            C = 4'b0001;
        end
        4'b0010: begin
            D = 4'b0000;
            C = 4'b0010;
        end
        4'b0011: begin
            D = 4'b0000;
            C = 4'b0011;
        end
        4'b0100: begin
            D = 4'b0001;
            C = 4'b0000;
        end
        4'b0101: begin
            D = 4'b0001;
            C = 4'b0001;
        end
        4'b0110: begin
            D = 4'b0001;
            C = 4'b0010;
        end
        4'b0111: begin
            D = 4'b0001;
            C = 4'b0011;
        end
        4'b1000: begin
            D = 4'b0010;
            C = 4'b0000;
        end
        4'b1001: begin
            D = 4'b0010;
            C = 4'b0001;
        end
        4'b1010: begin
            D = 4'b0010;
            C = 4'b0010;
        end
        4'b1011: begin
            D = 4'b0010;
            C = 4'b0011;
        end
        4'b1100: begin
            D = 4'b0011;
            C = 4'b0000;
        end
        4'b1101: begin
            D = 4'b0011;
            C = 4'b0001;
        end
        4'b1110: begin
            D = 4'b0011;
            C = 4'b0010;
        end
        4'b1111: begin
            D = 4'b0011;
            C = 4'b0011;
        end
    endcase
end

endmodule

module top_module (
    input [3:0] in0,
    input [3:0] in1,
    output [3:0] D,
    output [3:0] C
);

wire result;
wire [3:0] B_greater;

// Instantiate the comparator module
comparator comparator_inst(.in0(in0), .in1(in1), .result(result));

// Determine which input is greater
assign B_greater = (result) ? in0 : in1;

// Instantiate the binary_to_bcd module
binary_to_bcd binary_to_bcd_inst(.B(B_greater), .D(D), .C(C));

endmodule
