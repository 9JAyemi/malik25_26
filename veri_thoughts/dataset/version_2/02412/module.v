
module non_inverting_amp (
    input clk,
    input reset,
    input [15:0] sine_out,
    output reg [15:0] amp_out
);

    wire [15:0] Vplus = 16'h82A; // 1.65V

    always @(posedge clk) begin
        if (reset) begin
            amp_out <= 16'h0;
        end else begin
            amp_out <= Vplus * 10;
        end
    end

endmodule
