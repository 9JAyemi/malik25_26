module byte_swap_pipeline(
    input [31:0] in,
    input reset,
    input clk,
    output reg [31:0] out
);

reg [31:0] shift_reg [0:2];
reg [1:0] stage;

always @(*) begin
    case(stage)
        0: shift_reg[0] = in;
        1: shift_reg[1] = {shift_reg[0][23:0], shift_reg[0][31:24]};
        2: shift_reg[2] = {shift_reg[1][7:0], shift_reg[1][15:8], shift_reg[1][23:16], shift_reg[1][31:24]};
    endcase
end

always @(posedge clk) begin
    if(reset) begin
        stage <= 0;
    end else begin
        if(stage == 2) begin
            out <= shift_reg[2];
            stage <= 0;
        end else begin
            stage <= stage + 1;
        end
    end
end

endmodule