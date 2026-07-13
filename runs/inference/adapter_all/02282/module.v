
module shift_register (
    input clk,
    input [3:0] data_in,
    input shift_right,
    input load,
    output [3:0] data_out
);

reg [3:0] stage1, stage2, stage3, stage4;

always @(posedge clk) begin
    if (load) begin
        stage1 <= data_in;
        stage2 <= stage1;
        stage3 <= stage2;
        stage4 <= stage3;
    end else begin
        if (shift_right) begin
            stage1 <= stage4;
            stage2 <= stage1;
            stage3 <= stage2;
            stage4 <= stage3;
        end else begin
            stage1 <= stage2;
            stage2 <= stage3;
            stage3 <= stage4;
            stage4 <= data_in;
        end
    end
end

assign data_out = stage4;

endmodule
