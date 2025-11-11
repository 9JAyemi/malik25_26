module shift_register (
    input clk,
    input reset,            // Asynchronous reset
    input [3:0] d,
    input enable,
    output [3:0] q
);

reg [3:0] q_reg1, q_reg2, q_reg3, q_reg4;

always @(posedge clk, negedge reset) begin
    if (!reset) begin
        q_reg1 <= 1'b0;
        q_reg2 <= 1'b0;
        q_reg3 <= 1'b0;
        q_reg4 <= 1'b0;
    end else begin
        q_reg1 <= enable ? d[0] : q_reg1;
        q_reg2 <= enable ? q_reg1 : q_reg2;
        q_reg3 <= enable ? q_reg2 : q_reg3;
        q_reg4 <= enable ? q_reg3 : q_reg4;
    end
end

assign q = q_reg4;

endmodule