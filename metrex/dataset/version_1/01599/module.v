module mux_2_to_1 (
    input A,
    input B,
    input S,
    input clk,
    output reg Y
);

reg reg_A;
reg reg_B;

always @(posedge clk) begin
    reg_A <= A;
    reg_B <= B;
end

always @(posedge clk) begin
    if (S == 0) begin
        Y <= reg_A;
    end
    else begin
        Y <= reg_B;
    end
end

endmodule