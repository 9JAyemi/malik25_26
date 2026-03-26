
module johnson_counter (
    input clk,
    input reset,
    output reg [2:0] count
);

reg [2:0] count_reg1, count_reg2, count_reg3;

always @(posedge clk, posedge reset) begin
    if (reset) begin
        count_reg1 <= 3'b000;
        count_reg2 <= 3'b000;
        count_reg3 <= 3'b000;
    end else begin
        count_reg1 <= count_reg2;
        count_reg2 <= count_reg3;
        count_reg3 <= ~{count_reg2[1:0], count_reg2[2]};
    end
end

// Assign the output from the register
always @(*) begin
    count = count_reg1;
end

endmodule
