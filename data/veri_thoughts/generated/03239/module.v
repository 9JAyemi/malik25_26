
module top_module(
    input wire [15:0] in,
    output wire [7:0] out_hi,
    output wire [7:0] out_lo,
    input wire clk
);

    // Pipeline registers
    reg [15:0] stage1_out;
    reg [7:0] stage2_out_hi, stage2_out_lo;

    // Barrel shifter
    wire [15:0] shifted_data = in >> 8;

    // Clocked register for stage1_out
    always @(posedge clk) begin
        stage1_out <= shifted_data;
    end

    // Output registers
    always @(posedge clk) begin
        stage2_out_hi <= stage1_out[15:8];
        stage2_out_lo <= in[7:0];
    end

    // Output assignments
    assign out_hi = stage2_out_hi;
    assign out_lo = stage2_out_lo;

endmodule
