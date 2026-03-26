module signed_magnitude_adder (
    input signed [3:0] A,
    input signed [3:0] B,
    output signed [3:0] sum
);
    assign sum = A + B;
endmodule

module signed_mag_comparator (
    input signed [3:0] A,
    output eq,
    output lt,
    output gt
);
    assign eq = (A == 0);
    assign lt = (A < 0);
    assign gt = (A > 0);
endmodule

module top_module (
    input clk,
    input reset,
    input signed [3:0] A,
    input signed [3:0] B,
    input select,
    output reg signed [3:0] out
);
    wire signed [3:0] sum;
    wire eq, lt, gt;
    signed_mag_comparator comparator(A, eq, lt, gt);
    signed_magnitude_adder adder(A, B, sum);
    
    always @(posedge clk or posedge reset) begin
        if (reset) begin
            out <= 4'b0000;
        end else begin
            if (select) begin
                out <= {4'b0000, eq, lt, gt};
            end else begin
                out <= sum;
            end
        end
    end
endmodule