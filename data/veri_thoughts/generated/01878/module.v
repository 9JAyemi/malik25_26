
module mux_4to1_case (
    input A, B, C, D,
    input [1:0] sel,
    input clk,  // Added clock input
    output reg Y
);

reg [1:0] stage1_sel;
reg [1:0] stage2_sel;

always @(*) begin
    stage1_sel = sel;
    stage2_sel = stage1_sel;
end

always @(posedge clk) begin  // Corrected the event to use the clock input
    case (stage2_sel)
        2'b00: Y <= A;
        2'b01: Y <= B;
        2'b10: Y <= C;
        2'b11: Y <= D;
    endcase
end

endmodule
